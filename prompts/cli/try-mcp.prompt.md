# Try tools for the person's agent

Own `src/try-mcp.mjs`. Export `runMcp({cwd, words}={}, ports={})`, a newline-delimited stdio JSON-RPC MCP server returning exit code 0 after input closes and outstanding work finishes. Export `createTryTools({cwd,words}={}, ports={})` returning a `call(name,args)` interface for embedding and verification. This new interface preserves the existing Try, door and judge behavior.

The five tools are `try_open`, `try_state`, `try_run`, `try_check`, and `try_save_case`. Select the Git repository containing cwd and exactly one discovered Story test; optional `story` selects by the existing Story selection rules. Without it prefer the only open Try, otherwise the only test. If a Story matches multiple tests, prefer its only open Try; otherwise require the exact test path. Ambiguity names the choices and sends nothing. Open a missing or ended Try through runTry with no waiting or agent bridge. Reuse its private identity, session and source hashes. Refuse changed prompt or Story identity; never label uploaded old behavior as current source.

```mermaid
flowchart TD
 S[Select Story] --> O{Open Try?}
 O -->|No| N[Open through runTry]
 O -->|Yes| R[Read owner metadata]
 N --> R
 R --> V{Tool}
 V -->|Run| C[One door call]
 V -->|State or open| D[Current owner data]
 V -->|Check| J[Judge confirmed run]
 V -->|Save| A[Retain or save observed case]
```

State includes Story criteria, judge bindings, admitted entries and schemas, actual current saved data, known runs, server action history, budget metadata and judge progress. Read actual data from authenticated GET `/v1/try/ID/state` with `{world:...}`; never substitute initial test data when unavailable. Return a clear unavailable reason. Runs use runDoorCall once; preserve its confirmed before/after worlds and lossless result. `entry` is `prompt_path#operation`, `input` is a JSON object. Alternatively `argv` is a string array for the single admitted CLI entry, preserving words exactly. Never execute a project program or shell. Reject incompatible run arguments and unknown entries before dispatch. Every run spends the existing Try budget and appears in the server history through the door API. No automatic retry of an uncertain run; block subsequent runs in this connection after a door error carrying unknownOutcome: true, regardless of its message text.

Check a named confirmed run or the last run using createRunJudge; report unsupported checks honestly. Saving selects a Story criterion explicitly, or uses the unique criterion tied to the entry. Save an isolated scenario through saveDoorCase with the confirmed before-world, original simulation/context and criteria, and one exact observed-result step; leave the original scenario untouched. Refuse saving when the before-world is missing. For partial Story coverage, prominently report "Recorded case; covers N of M Story criteria. Complete coverage before pdd test"; this recorded case is not claimed to pass runtime admission. Save records an observation, does not approve a prompt and does not claim the result is correct. Repeated save of the same run is a no-op. Explain saved-data setup needs review when the before-world is nonempty.

Expose honest MCP annotations: open/run/save change state, check/state are read-only observations although state can open a missing Try. All tools accept optional `story`; run accepts `entry`, `input`, `argv`; check/save accept optional `run_id`; save accepts optional `criterion_id` and `name`. Reject extra fields and malformed values. Tool failures are MCP `isError` results, not protocol crashes. Serialize tool calls so simultaneous mutations cannot open or run twice accidentally. Replayed JSON-RPC request IDs return the same response without redispatch; conflicting reuse is an invalid request. Keep stdout exclusively JSON-RPC. Send readable errors/progress to stderr, and `notifications/progress` only for a caller-supplied progress token. Emit progress during slow tools and clear timers afterwards.

`try_save_case` also accepts an explicit retained-case apply mode: paired string
arguments `pending_id` and `closed_editor_for`. `pending_id` is the existing
received-case identity, two lowercase 64-hex components separated by a dot;
`closed_editor_for` is a nonempty exact repository-relative original test path.
The ordinary argument validator requires both and rejects `story`, `run_id`,
`criterion_id` and `name` in this mode, plus all unknown fields. With neither new
argument, preserve the current confirmed-run staging operation. Either new
argument alone is invalid; no implicit last-run apply or replacement target.

The tool description must state that `closed_editor_for` represents the person's
actual confirmation that this named file is closed and handed over until the
apply finishes. Obtain that specific confirmation; a physical close, missing
lock, saved payload, generic tool approval or unrelated earlier message is not
confirmation. It coordinates writing and does not approve expectations.

Branch to the runtime client's [local retained-case application](runtime-client.prompt.md#local-retained-case-application)
before `readTryOwner`, remote metadata or in-memory run lookup. Delegate with the
server's `cwd`, explicit pending identity, the existing local closed-editor
handoff type and invocation signal. Never supply a JSON opaque lease or rebuild
the payload. This mode also works after MCP restart without a run in memory;
it makes no HTTP/model/Runtime request and does not open a Try.
It performs no gh authentication or credential lookup and requires no sign-in.

Only the owner's typed committed result is success, including an established
duplicate no-op; return its identical printable result associated with
`pending_id`. Format the warning solely from the owner's coverage projection.
For `original-story`, use the existing "Recorded case; covers N of M Story
criteria" warning. For `retained-scenario`, say "Recorded case; references N of M
retained scenario criteria. Whole-Story coverage is unavailable." For
`unavailable`, say "Recorded case; criterion coverage is unavailable." In the
latter two cases require completion of coverage before `pdd test`; keep the
observed-output, expectation and saved-data review reminder in every case.
Neither count nor warning claims passed criteria or current-source proof.
Ordinary confirmed-run save wording/counts remain unchanged. Do not parse a
message, read current Story criteria or change transaction outcome to fill
missing coverage. Pending/conflict is an
MCP `isError` with the owner's actual identity, reason and recovery location;
failure is an error without an invented pending result. Reuse owner outcome
classification and formatting, not English-message parsing or a second policy.
Use a fresh JSON-RPC request ID for an apply attempt while preserving the pending
identity; existing response replay and conflicting-ID refusal still apply.

Support initialize with version negotiation (2025-06-18, 2025-03-26, 2024-11-05; default newest), ping, tools/list, tools/call and notifications. Invalid JSON gets -32700, invalid envelopes -32600, invalid method parameters -32602, unknown methods -32601. Ignore valid notifications without executing tool calls. Reject batches. Bound incoming lines and response replay memory; never print tokens, stacks or private owner URLs. Closing input waits for queued requests; it does not close the Try.

## Workspace and save association

Carry the [workspace authority](runtime-workspace.prompt.md) through owner lookup, source refresh and every tool. Required source validation precedes authentication, model metadata or dispatch. Exact original selected test/session association comes from the runtime client, never the first test for a Story. Durable received-case import, not an in-memory saved flag, owns duplicate safety.

Preserve the current isolated observed-world save operation. It still uses the native save transaction and bounded no-link variant target, retains original test association and requires the confirmed `world_before`. When an exact-original append is requested, delegate to the runtime client: if that starting world cannot hold after the authored prior steps, retain the case pending. Do not change original `initial_world`, invent reset steps or silently substitute a variant for requested append. An explicitly selected isolated variant remains a separate reviewed action with honest partial coverage.


## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.

- [Runtime client](runtime-client.prompt.md): required generation/runtime/verification context for selection, owner identity, opening, current owner reads, door execution, safe case append and local retained-case application through `applyPendingCaseWithHandoff`.
- [Runtime preflight](runtime-preflight.prompt.md): required generation/runtime context for Story selection.
- [Agent judge](agent-judge.prompt.md): required generation/runtime context for per-run comparison and progress.
- [Prompting guide](../../docs/prompting-guide.md): required authoring context.

Runtime transport: in Runtime checks, `createTryTools({cwd, words})` is a `prompt-runtime.interface.v2` `TryTools` factory (raising `invalid-try-tools-cwd` when `cwd` is empty) that stores `{cwd, words, runs: [], unknown: false}` via `instances.store({handle, state})` under the executor-issued `instance_handle` and returns `{handle}`. Instance method `call({handle, name, args})` loads state via `instances.load({handle})`, validates `name` and `args` (raising `invalid-tool-call` on unknown tools, invalid arguments, unknown entries, blocked `unknown` sessions, missing runs or failed pending application), delegates `try_save_case` with `pending_id` and `closed_editor_for` to `client.pendingApply({cwd, pendingId, testPath})`, otherwise reads the Try owner via `client.ownerRead({cwd, story})`, dispatches `try_run` via `client.doorCall({sessionId, entry, input})`, saves confirmed runs via `client.caseSave({root, runId, criterionId})`, updates instance state via `instances.store({handle, state})`, and returns `{result}` containing the tool response object. `runMcp({cwd, words})` raises `invalid-mcp-cwd` when `cwd` is empty, reads JSON-RPC input lines via `stdio.readLines({cwd})`, writes JSON-RPC responses (each ending with `\n`) via `stdio.stdout({text})` and progress/diagnostics via `stdio.stderr({text})`, and returns `{exitCode: 0}`. Native readline stream lifecycle and interval timers stay in `test/try-mcp.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "11884aa5769f109307178e3186512c58ce118705cddec07554dadf00c13590aa",
  "entries": [
    {
      "operation": "createTryTools",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "words": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "cwd",
          "words"
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
      "errors": [
        "invalid-try-tools-cwd"
      ],
      "instance": {
        "kind": "factory",
        "type": "TryTools",
        "path": "/handle"
      },
      "resource_operations": [
        "instances.store"
      ]
    },
    {
      "operation": "call",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "name": {
            "type": "string"
          },
          "args": {
            "type": "object",
            "properties": {
              "story": {
                "type": "string"
              },
              "entry": {
                "type": "string"
              },
              "input": {
                "type": "object",
                "properties": {
                  "orderId": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "argv": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "run_id": {
                "type": "string"
              },
              "criterion_id": {
                "type": "string"
              },
              "name": {
                "type": "string"
              },
              "pending_id": {
                "type": "string"
              },
              "closed_editor_for": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "handle",
          "name",
          "args"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "result": {
            "type": "object",
            "properties": {
              "try_id": {
                "type": "string"
              },
              "story": {
                "type": "string"
              },
              "story_path": {
                "type": "string"
              },
              "test_path": {
                "type": "string"
              },
              "run_id": {
                "type": "string"
              },
              "passed": {
                "type": "boolean"
              },
              "saved": {
                "type": "string"
              },
              "committed": {
                "type": "boolean"
              },
              "message": {
                "type": "string"
              },
              "covered": {
                "type": "integer"
              },
              "total": {
                "type": "integer"
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "result"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-tool-call"
      ],
      "instance": {
        "kind": "method",
        "type": "TryTools",
        "path": "/handle"
      },
      "resource_operations": [
        "instances.load",
        "instances.store",
        "client.ownerRead",
        "client.doorCall",
        "client.caseSave",
        "client.pendingApply"
      ]
    },
    {
      "operation": "runMcp",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "words": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "cwd",
          "words"
        ],
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
      "errors": [
        "invalid-mcp-cwd"
      ],
      "resource_operations": [
        "stdio.readLines",
        "stdio.stdout",
        "stdio.stderr"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "instances",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              },
              "state": {
                "type": "object",
                "properties": {
                  "cwd": {
                    "type": "string"
                  },
                  "words": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "runs": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "additionalProperties": false,
                      "properties": {},
                      "required": []
                    }
                  },
                  "unknown": {
                    "type": "boolean"
                  }
                },
                "required": [
                  "cwd",
                  "words",
                  "runs",
                  "unknown"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "handle",
              "state"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "state": {
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
              }
            },
            "required": [
              "state"
            ],
            "additionalProperties": false
          },
          "name": "store"
        },
        {
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
              "state": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "cwd": {
                        "type": "string"
                      },
                      "words": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "runs": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "additionalProperties": false,
                          "properties": {},
                          "required": []
                        }
                      },
                      "unknown": {
                        "type": "boolean"
                      }
                    },
                    "required": [
                      "cwd",
                      "words",
                      "runs",
                      "unknown"
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
              "state"
            ],
            "additionalProperties": false
          },
          "name": "load"
        }
      ]
    },
    {
      "name": "client",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "story": {
                "type": "string"
              }
            },
            "required": [
              "cwd",
              "story"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              },
              "tryId": {
                "type": "string"
              },
              "story": {
                "type": "string"
              },
              "storyPath": {
                "type": "string"
              },
              "testPath": {
                "type": "string"
              },
              "criteria": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": {
                      "type": "string"
                    },
                    "text": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "id",
                    "text"
                  ],
                  "additionalProperties": false
                }
              },
              "entries": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "world": {
                "type": "object",
                "properties": {
                  "orders": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "root",
              "tryId",
              "story",
              "storyPath",
              "testPath",
              "criteria",
              "entries",
              "world"
            ],
            "additionalProperties": false
          },
          "name": "ownerRead"
        },
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "sessionId": {
                "type": "string"
              },
              "entry": {
                "type": "string"
              },
              "input": {
                "type": "object",
                "properties": {
                  "orderId": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "sessionId",
              "entry",
              "input"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              },
              "result": {
                "type": "object",
                "properties": {
                  "ok": {
                    "type": "boolean"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "inputWorld": {
                "type": "object",
                "properties": {
                  "orders": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "world": {
                "type": "object",
                "properties": {
                  "orders": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "id",
              "result",
              "inputWorld",
              "world"
            ],
            "additionalProperties": false
          },
          "name": "doorCall"
        },
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              },
              "runId": {
                "type": "string"
              },
              "criterionId": {
                "type": "string"
              }
            },
            "required": [
              "root",
              "runId",
              "criterionId"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "saved": {
                "type": "string"
              }
            },
            "required": [
              "saved"
            ],
            "additionalProperties": false
          },
          "name": "caseSave"
        },
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "pendingId": {
                "type": "string"
              },
              "testPath": {
                "type": "string"
              }
            },
            "required": [
              "cwd",
              "pendingId",
              "testPath"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "committed": {
                "type": "boolean"
              },
              "message": {
                "type": "string"
              },
              "covered": {
                "type": "integer"
              },
              "total": {
                "type": "integer"
              }
            },
            "required": [
              "committed",
              "message",
              "covered",
              "total"
            ],
            "additionalProperties": false
          },
          "name": "pendingApply"
        }
      ]
    },
    {
      "name": "stdio",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "access": "write",
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
          "name": "readLines"
        },
        {
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
          },
          "name": "stdout"
        },
        {
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
          },
          "name": "stderr"
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 24,
    "max_model_calls": 12
  },
  "conventions": [
    {
      "path": "/entries/0/result_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/1/input_schema/properties/handle",
      "convention": "handle"
    }
  ],
  "schema_version": "prompt-runtime.interface.v2",
  "instance_types": [
    {
      "name": "TryTools",
      "resource": "instances"
    }
  ]
}
```
</details>
