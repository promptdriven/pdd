# Workflow areas

Own `src/workflow-areas.mjs`. A workflow is a skill folder `pdd-NAME/` with a `workflow.json` file:

`{"version":2,"areas":[{"name":"plan","steps":["scope"],"optional":[],"gate":"approve"},{"name":"build","steps":["change","verify"],"optional":[],"gate":"pr"}]}`

pdd looks for `pdd-NAME/workflow.json` in these skill folders, in this order, and the first one wins:
1. `<project>/.agents/skills`
2. `<project>/.claude/skills`
3. `<home>/.agents/skills`
4. `<home>/.claude/skills`
5. `<packageRoot>/skills`

A home skill folder never overrides a workflow that the package ships (same `pdd-NAME` with a `workflow.json` in `<packageRoot>/skills`): such a copy comes from `npx skills add` or `pdd setup` and may be old, with or without pdd's `.pdd-skill.json` marker. Only a project folder overrides a bundled workflow. Home folders add workflows that the package does not have (a person's own `pdd-docs`).

`<project>` is the nearest folder at or above `cwd` that has a `.git` entry; outside a repository there is no project folder. A person can copy a bundled workflow skill to `pdd-docs` in one of these folders and run `pdd workflow run docs N`.

- `readWorkflowAreas({packageRoot, name, cwd, home})` returns `{name, skill, dir, source, areas}`. `skill` is `pdd-NAME`, `dir` is the skill folder that won, `source` is project, home or package. Each area is `{name, steps, optional, gate}`.
- `listWorkflowAreas({packageRoot, cwd, home})` returns every workflow found with the same lookup, sorted by name.
- `formatWorkflowList(list, {json})` returns text. JSON is `{"workflows":[{"name","skill","source","dir","areas"}],"default":null}`. Plain text is one line per workflow with its areas, gates (a `before` approval shows as `approve → pr`) and source, then "Listing starts no work. Use pdd workflow run NAME ISSUE."

Check the shape: version 2; at least one area; names and steps are lowercase words joined by single hyphens; `optional` steps are in `steps`; the last area has gate `pr`; every other area has gate `approve`, or gate `pr` with `"then":"ask-code"` (pdd opens PR 1 there and asks whether to go on to the code area). Keep `then` in the returned area. A `pr` area may also have `"before":"approve"`: the person approves the area before pdd opens its PR (0.1.4: Try before PR 1). Keep `before` in the returned area; any other `before` is invalid. An invalid file that wins the lookup throws an error that names the workflow and the file. An unknown name throws an error that lists the known workflows.

## Structured replay opt-in

A pr area may explicitly set replay_evidence to `pdd.replay-evidence.v1`. Preserve this exact field in returned
areas and saved runs. Reject an unsupported version or a policy on a non-pr area. The bundled feature/bug
code areas set it; small-change and custom areas have no implicit policy. Never retrofit a policy onto a
saved area from the current package. [Replay evidence](workflow-replay.prompt.md) owns the manifest contract.

## Approval gate advisory

Own detection of a workflow with no approval gate before implementation. An area `gate: "approve"` or `before: "approve"` provides the explicit approval boundary; `then: "ask-code"` also provides a boundary before its following area. If none of these exists, return optional `warnings` containing one plain advisory that names the workflow and says it has no approve gate before code. This includes a valid custom single-area `pr` workflow. Do not reject, insert a gate, reorder steps or prevent startup. Workflows with a boundary retain their existing returned shape (no warning field required). Preserve all existing exports and inputs; this optional string-array field on a workflow is the only result addition. Listing renders the advisory in plain text and retains it in each affected JSON workflow; the runner displays it on startup. Detection policy belongs here, not in the runner.

## Dependencies

- [Replay evidence](workflow-replay.prompt.md): owns the `pdd.replay-evidence.v1` manifest contract.
- In Runtime checks, `files.stat({path})` and `files.read({path})` inspect `.git` markers and `pdd-NAME/workflow.json` files across project, home and package skill folders, and `fs.readdir({path})` returns `{entries}` for each skill root directory. `readWorkflowAreas` fails with `workflow_unknown` when no skill folder defines the requested workflow and `workflow_invalid` when the winning `workflow.json` violates the shape rules; `listWorkflowAreas` returns `{workflows}` and fails with `workflow_invalid` when any winning `workflow.json` violates the shape rules; `formatWorkflowList({list, options})` returns `{text}` and fails with `invalid_workflow_list` when a workflow record has an empty `areas` array. Native filesystem permissions and symlink traversal stay in `test/workflow-areas.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "6c921aa903031205bbf888eae3974339a8a069114378fc2cb1654c9243b9c952",
  "entries": [
    {
      "operation": "readWorkflowAreas",
      "input_schema": {
        "type": "object",
        "properties": {
          "packageRoot": {
            "type": "string"
          },
          "name": {
            "type": "string"
          },
          "cwd": {
            "type": "string"
          },
          "home": {
            "type": "string"
          }
        },
        "required": [
          "packageRoot",
          "name",
          "cwd",
          "home"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "name": {
            "type": "string"
          },
          "skill": {
            "type": "string"
          },
          "dir": {
            "type": "string"
          },
          "source": {
            "type": "string",
            "enum": [
              "project",
              "home",
              "package"
            ]
          },
          "areas": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "name": {
                  "type": "string"
                },
                "steps": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "optional": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "gate": {
                  "type": "string",
                  "enum": [
                    "approve",
                    "pr"
                  ]
                },
                "before": {
                  "type": "string",
                  "enum": [
                    "approve"
                  ]
                },
                "then": {
                  "type": "string",
                  "enum": [
                    "ask-code"
                  ]
                },
                "replay_evidence": {
                  "type": "string",
                  "enum": [
                    "pdd.replay-evidence.v1"
                  ]
                }
              },
              "required": [
                "name",
                "steps",
                "optional",
                "gate"
              ],
              "additionalProperties": false
            }
          },
          "warnings": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "name",
          "skill",
          "dir",
          "source",
          "areas"
        ],
        "additionalProperties": false
      },
      "errors": [
        "workflow_unknown",
        "workflow_invalid"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "fs.readdir"
      ]
    },
    {
      "operation": "listWorkflowAreas",
      "input_schema": {
        "type": "object",
        "properties": {
          "packageRoot": {
            "type": "string"
          },
          "cwd": {
            "type": "string"
          },
          "home": {
            "type": "string"
          }
        },
        "required": [
          "packageRoot",
          "cwd",
          "home"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "workflows": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "name": {
                  "type": "string"
                },
                "skill": {
                  "type": "string"
                },
                "dir": {
                  "type": "string"
                },
                "source": {
                  "type": "string",
                  "enum": [
                    "project",
                    "home",
                    "package"
                  ]
                },
                "areas": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "name": {
                        "type": "string"
                      },
                      "steps": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "optional": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "gate": {
                        "type": "string",
                        "enum": [
                          "approve",
                          "pr"
                        ]
                      },
                      "before": {
                        "type": "string",
                        "enum": [
                          "approve"
                        ]
                      },
                      "then": {
                        "type": "string",
                        "enum": [
                          "ask-code"
                        ]
                      },
                      "replay_evidence": {
                        "type": "string",
                        "enum": [
                          "pdd.replay-evidence.v1"
                        ]
                      }
                    },
                    "required": [
                      "name",
                      "steps",
                      "optional",
                      "gate"
                    ],
                    "additionalProperties": false
                  }
                },
                "warnings": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                }
              },
              "required": [
                "name",
                "skill",
                "dir",
                "source",
                "areas"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "workflows"
        ],
        "additionalProperties": false
      },
      "errors": [
        "workflow_invalid"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "fs.readdir"
      ]
    },
    {
      "operation": "formatWorkflowList",
      "input_schema": {
        "type": "object",
        "properties": {
          "list": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "name": {
                  "type": "string"
                },
                "skill": {
                  "type": "string"
                },
                "dir": {
                  "type": "string"
                },
                "source": {
                  "type": "string",
                  "enum": [
                    "project",
                    "home",
                    "package"
                  ]
                },
                "areas": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "name": {
                        "type": "string"
                      },
                      "steps": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "optional": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "gate": {
                        "type": "string",
                        "enum": [
                          "approve",
                          "pr"
                        ]
                      },
                      "before": {
                        "type": "string",
                        "enum": [
                          "approve"
                        ]
                      },
                      "then": {
                        "type": "string",
                        "enum": [
                          "ask-code"
                        ]
                      },
                      "replay_evidence": {
                        "type": "string",
                        "enum": [
                          "pdd.replay-evidence.v1"
                        ]
                      }
                    },
                    "required": [
                      "name",
                      "steps",
                      "optional",
                      "gate"
                    ],
                    "additionalProperties": false
                  }
                },
                "warnings": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                }
              },
              "required": [
                "name",
                "skill",
                "dir",
                "source",
                "areas"
              ],
              "additionalProperties": false
            }
          },
          "options": {
            "type": "object",
            "properties": {
              "json": {
                "type": "boolean"
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "list"
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
        "invalid_workflow_list"
      ],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "files",
      "kind": "blob",
      "access": "read",
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
    }
  ],
  "limits": {
    "max_steps": 32,
    "max_model_calls": 12
  },
  "conventions": []
}
```
</details>
