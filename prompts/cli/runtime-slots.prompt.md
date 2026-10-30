# Shared local runtime slots

Own `src/runtime-slots.mjs`: admit independent local pdd jobs fairly under one person's runtime limit, and expose a local snapshot for `pdd jobs`. New public module functions below accept injected ports; no client transport, paid execution or batch policy belongs here. Preserve the client's existing private state safety and dispatch evidence.

## Reservations and waiting

Use `<stateDir>/slots/<encoded URL.host>/`, where stateDir is the caller's resolved PDD_STATE_DIR (default ~/.pdd/runtime), and URL.host includes a port when present. Encode the host with encodeURIComponent as one path component; repositories/worktrees sharing this folder share the limit. Folders 0700 and files 0600, no credentials or source archives. `PDD_MAX_JOBS` is a positive safe integer, default 4; an invalid value warns and uses 4 rather than adding a command refusal.

Module function `acquireRuntimeSlot({stateDir,origin,limit,kind,deadline}, ports)` returns a reservation `{id,directory}` or null if the caller wait ends/interruption occurs before acquisition. kind is check, lint or try; deadline is an absolute millisecond timestamp or null for no deadline. Supply pid, isAlive(pid), now(), randomUUID(), sleep(ms), interrupted(), files and readRun(id) as ports. files supplies listRecords({directory}), exclusiveCreate(path,record), writeAtomic(path,record) and unlink(path); isAlive supplies process liveness. Native defaults use process/file/clock operations; no network implementation is hidden in this helper. The client supplies authenticated readRun, returning ended, running or unknown for that exact ID.

One durable ticket per waiting job retains its original timestamp through contention. Order live tickets by creation time, then stable ticket ID for equal times, never directory enumeration. Only the oldest live ticket can claim the next free slot. Atomically exclude competing claimants using exclusive create; rescan under that exclusion before assigning. Failed contention keeps the same ticket. A job has one ticket or one active reservation, never duplicates. A dead waiter's ticket can be removed. Print changing queue status through say(line), e.g. `Waiting for a local slot: 4 of 4 busy, 2 ahead of you. (Set PDD_MAX_JOBS to change the limit.)`; all progress goes to stderr in the caller.

An active record holds its unique id, state active, owner pid, kind, started_at (epoch milliseconds), and request_ids. Module function `recordRuntimeRequest(reservation, requestId, ports)` durably appends the ID without duplicates before dispatch, preserving earlier IDs. Module function `releaseRuntimeSlot(reservation, {ended}, ports)` releases only when ended is confirmed, or no dispatch was possible; ended false retains the record. Local timeout/interruption does not prove a posted job ended. Remove an interrupted waiter's ticket without releasing another job's reservation.

A live owner's active reservation stays occupied. A dead owner's reservation stays occupied while any recorded runtime job is running/unknown, or evidence is missing/wrong-ID/unreadable. It may be reclaimed when all recorded jobs are confirmed ended, or at age >= 30 minutes from started_at. A dead owner with no request IDs is safely unsent. A confirmed service-restarted terminal receipt counts as ended for this lease; the client separately owns replacement authorization. Never infer completion from process death alone. Cleanup and claim updates remain private and atomic; do not delete another claimant's record.

## Local inspection

Module function `listRuntimeJobs({stateDir,origin}, ports={})` calls `ports.files.listRecords({directory})` exactly once with the resolved host folder above, and returns `{jobs}`. The native files port reads the private active/ticket records and normalizes each to `{id,state,pid,kind,started_at,request_ids}`; absent folder means an empty list. Incomplete/unreadable state throws an error with code local-state-unavailable, never silently shown as no work. Wrap files.listRecords read failures with that same code. Listing neither reclaims records nor contacts gh/runtime/processes. Return active rows first, then waiting, ordered within each state by started_at and id. Preserve record IDs, PIDs, request IDs and timestamps. The declared port is this actual filesystem dependency, not an admission decision supplied by a test.

Module function `runJobs({env}, {stdout,stderr,files}={})` resolves the same default state directory and uses the existing public runtimeOrigin(env) export of src/runtime-client.mjs for the runtime origin (no sign-in or network effect) and calls listRuntimeJobs. It requires no repository or authentication. Print active/waiting rows with kind, PID, age and request IDs, or a plain empty message; return 0. Read errors print a finite cause on stderr and return 5; do not present a successful empty snapshot. Output lines end with a newline. No additional command options are introduced.

## Dependencies

- [Lock pattern](workflow-herdr-layout.prompt.md): required generation/verification context only for native exclusive-create/process-liveness conventions; its Herdr location/policy is not this module's policy.

Only listRuntimeJobs is bound below. The files.listRecords resource uses write access solely so port.write can record the supplied read arguments as a spy; the real dependency only reads slot records and does not mutate them. Its native function receives the ordinary ports argument; the Runtime transport serializes the options and binds files.listRecords. Acquisition, atomic exclusion, crash consistency, process death and native runJobs formatting require ordinary Node/child-process tests. A prompt replay of a supplied snapshot proves ordering/forwarding only.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "f987a1bc66095525362c0f260b2ebc07137b885916ea59490bd89d54cf102520",
  "entries": [
    {
      "operation": "listRuntimeJobs",
      "input_schema": {
        "type": "object",
        "properties": {
          "stateDir": {
            "type": "string"
          },
          "origin": {
            "type": "string"
          }
        },
        "required": [
          "stateDir",
          "origin"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "jobs": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "state": {
                  "type": "string",
                  "enum": [
                    "active",
                    "waiting"
                  ]
                },
                "pid": {
                  "type": "integer",
                  "minimum": 1
                },
                "kind": {
                  "type": "string",
                  "enum": [
                    "check",
                    "lint",
                    "try"
                  ]
                },
                "started_at": {
                  "type": "integer",
                  "minimum": 0
                },
                "request_ids": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                }
              },
              "required": [
                "id",
                "state",
                "pid",
                "kind",
                "started_at",
                "request_ids"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "jobs"
        ],
        "additionalProperties": false
      },
      "errors": ["local-state-unavailable"]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "files",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "listRecords",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "directory": {
                "type": "string"
              }
            },
            "required": [
              "directory"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "jobs": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": {
                      "type": "string"
                    },
                    "state": {
                      "type": "string",
                      "enum": [
                        "active",
                        "waiting"
                      ]
                    },
                    "pid": {
                      "type": "integer",
                      "minimum": 1
                    },
                    "kind": {
                      "type": "string",
                      "enum": [
                        "check",
                        "lint",
                        "try"
                      ]
                    },
                    "started_at": {
                      "type": "integer",
                      "minimum": 0
                    },
                    "request_ids": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    }
                  },
                  "required": [
                    "id",
                    "state",
                    "pid",
                    "kind",
                    "started_at",
                    "request_ids"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "jobs"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 4,
    "max_model_calls": 4
  },
  "conventions": []
}
```
</details>
