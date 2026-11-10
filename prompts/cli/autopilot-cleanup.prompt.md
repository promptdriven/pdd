# Remove ended run worktrees safely

Own `src/autopilot-cleanup.mjs`. Export async `cleanupWorktrees({cwd,repository},ports={})`
returning `{removed, kept}` arrays of run IDs. Use injectable listRuns, lookup,
readRun, lock and execute ports; defaults use existing run listing (including
cancelled archives), allocator identity lookup, saved records, existing run lock
and bounded native subprocesses. Each failure keeps the worktree and continues.
For an archived cancelled record whose saved runDir points to a replacement,
resolve the existing RUN_DIR-cancelled-RUN_ID_PREFIX folder (first eight run ID
characters). Require the full ended identity to match, then lock and re-read that
archive. Do not lock or mutate the replacement run.
Only same-repository completed/cancelled runs with no gate and with root, branch,
runDir and runId may qualify. Never remove the invoking checkout or any root
referenced by a waiting/running/paused/stuck/question run. Lock the candidate run
and re-read the same ended identity before inspection and immediately before
removal. Verify original allocation via lookupIssueWorktree and require matching
root, branch and runId. Require at least one PR for this exact head branch in the
same repository and every PR closed or merged (read-only gh pr list --state all,
--head branch). Unknown or open means keep.

Require git status --porcelain=v1 --untracked-files=all empty, an upstream, and
rev-list --count @{upstream}..HEAD equal zero. Check the branch still matches and
HEAD equals the remote-tracking upstream commit immediately before removal.
A branch behind its upstream is conservatively retained. Do not fetch or push.
Remove only through git worktree remove ROOT from the owning source checkout,
without force. Do not delete branches, claims, run records or allocation evidence.
Keep locked, dirty, untracked, unpushed, detached, replaced or unknown worktrees.

## Dependencies

- [Run records](workflow-runs.prompt.md): native generation and verification context for listRuns and readRun.
- [Allocator](workflow-worktree.prompt.md): native generation and verification context for lookupIssueWorktree identity.
- [Workflow runner](workflow-runner.prompt.md): native generation and verification context for acquireRunLock.
- [Agent adapters](agent-adapters.prompt.md): native generation and verification context for bounded process execution.

In the Runtime interface, `cleanupWorktrees({cwd, repository})` uses `runs.listRuns({cwd, cancelled})`, `runs.readRun({runDir})`, `runs.lookup({cwd, runId, branch})`, `runs.lock({runDir})` and `process.execute({file, args, cwd})` (`gh pr list`, `git symbolic-ref`, `git status`, `git rev-list`, `git rev-parse`, `git worktree remove`), returning `{removed, kept}` arrays of run IDs without throwing. Native lock-file release callbacks and child-process execution stay a native obligation covered by `test/autopilot-cleanup.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "7f7300aea95b7252a48f8e008e249a0340410a10b5509123d74e0295e9674a35",
  "entries": [
    {
      "operation": "cleanupWorktrees",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "repository": {
            "type": "string"
          }
        },
        "required": [
          "cwd",
          "repository"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "removed": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "kept": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "removed",
          "kept"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "runs.listRuns",
        "runs.readRun",
        "runs.lookup",
        "runs.lock",
        "process.execute"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "runs",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "listRuns",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "cancelled": {
                "type": "boolean"
              }
            },
            "required": [
              "cwd",
              "cancelled"
            ],
            "additionalProperties": false
          },
          "result_schema": {
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
                    "root": {
                      "type": "string"
                    },
                    "branch": {
                      "type": "string"
                    },
                    "runDir": {
                      "type": "string"
                    },
                    "sourceRoot": {
                      "type": "string"
                    },
                    "state": {
                      "type": "string"
                    },
                    "repo": {
                      "type": "string"
                    },
                    "gate": {
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
                    "root",
                    "branch",
                    "runDir",
                    "sourceRoot",
                    "state",
                    "repo",
                    "gate"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "runs"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "readRun",
          "access": "read",
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
              "run": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "runId": {
                        "type": "string"
                      },
                      "root": {
                        "type": "string"
                      },
                      "branch": {
                        "type": "string"
                      },
                      "runDir": {
                        "type": "string"
                      },
                      "sourceRoot": {
                        "type": "string"
                      },
                      "state": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "gate": {
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
                      "root",
                      "branch",
                      "runDir",
                      "sourceRoot",
                      "state",
                      "repo",
                      "gate"
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
          }
        },
        {
          "name": "lookup",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "runId": {
                "type": "string"
              },
              "branch": {
                "type": "string"
              }
            },
            "required": [
              "cwd",
              "runId",
              "branch"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "state": {
                "type": "string"
              },
              "assignment": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "worktreePath": {
                        "type": "string"
                      },
                      "branch": {
                        "type": "string"
                      },
                      "runId": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "worktreePath",
                      "branch",
                      "runId"
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
              "state",
              "assignment"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "lock",
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
      "access": "write",
      "operations": [
        {
          "name": "execute",
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
              }
            },
            "required": [
              "code",
              "stdout"
            ],
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
