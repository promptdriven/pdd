# Local module binding inventory

Own `src/runtime-bindings.mjs`, exporting `bindingCoverage({root, found, selected, includeRuntime=false})`.
Implement the local inventory contract in [runtime bindings](../../docs/runtime-bindings.md): limit the file to 64 KiB and 1000 module declarations; validate the complete inventory before any network or sign-in, including safe Git-visible regular paths without symlink ancestors, exact keys, known Stories and unique declarations. Throw `PreflightError` exit 4 for malformed declarations with the module/path and reason. Return `{available,bound,total,modules}` for modules intersecting selected Stories; absent inventory returns false/null/null/empty. A selected prompt declaration must reach an executable Runtime interface through the selected tests' entries and declared calls. Validate declaration shape and paths even for unselected modules; only selected declarations require selected reachability. Preserve declaration order.

## Workspace inventory use

Use the [workspace authority](runtime-workspace.prompt.md) before reading any declared source, prompt or Story. The root binding inventory is local control metadata, never permission for excluded source or automatic context. Preserve complete inventory shape/identity validation and strict executable no-link rules; optional excluded source is not opened just to compute coverage. Mark affected selected coverage unavailable with its cause instead of manufacturing a bound count or globally refusing unrelated selected work. A selected required prompt crossing remains a local preflight refusal.


## Dependencies

- [Runtime prompt inventory](interface-draft.prompt.md#inventory-results): required generation and verification context for the additive repository `runtime` coverage shape and counting rules.

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.

- [Inventory contract](../../docs/runtime-bindings.md), required for generation and verification.
- [Preflight](runtime-preflight.prompt.md), required for the existing `PreflightError` and `readPrompt` exports and discovery record shapes.

## Runtime prompt coverage

Preserve the default `{available,bound,total,modules}` result for inventory consumers. Only `includeRuntime: true` composes the interface drafting owner's repository coverage as additive `runtime`, including absent inventory. The CLI requests this option; inventory-only consumers do not scan unrelated prompts. Preserve module binding semantics.

In Runtime checks, `git.listFiles({root})` supplies the repository's Git-visible relative file list (raising `source-unavailable` when `status` is nonzero), and `files.stat({path})` and `files.read({path})` inspect blobs under `<root>/<path>` (including `<root>/pdd-workspace.json`, `<root>/pdd-bindings.json`, declared modules, Stories and prompts). Malformed or unreachable binding declarations raise `PreflightError`; invalid workspace policy raises `workspace-config-invalid`. Physical symlink-ancestor traversal stays in `test/runtime-bindings-edges.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "ada6651dcbff1b334b2e6b64645b4789c1c00a56bb8a9282f4c61bf7717771f4",
  "entries": [
    {
      "operation": "bindingCoverage",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          },
          "found": {
            "type": "object",
            "properties": {
              "visible": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "stories": {
                "type": "array",
                "items": {
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
                }
              }
            },
            "required": [
              "visible",
              "stories"
            ],
            "additionalProperties": false
          },
          "selected": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "storyPath": {
                  "type": "string"
                },
                "doc": {
                  "type": "object",
                  "properties": {
                    "steps": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "entry_path": {
                            "type": "string"
                          }
                        },
                        "required": [
                          "entry_path"
                        ],
                        "additionalProperties": false
                      }
                    }
                  },
                  "required": [
                    "steps"
                  ],
                  "additionalProperties": false
                }
              },
              "required": [
                "storyPath",
                "doc"
              ],
              "additionalProperties": false
            }
          },
          "includeRuntime": {
            "type": "boolean"
          }
        },
        "required": [
          "root",
          "found",
          "selected"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "available": {
            "type": "boolean"
          },
          "bound": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          },
          "total": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          },
          "modules": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": {
                  "type": "string"
                },
                "state": {
                  "type": "string",
                  "enum": [
                    "bound",
                    "unbound"
                  ]
                },
                "reason": {
                  "type": "string"
                },
                "port_attempt": {
                  "type": "string"
                }
              },
              "required": [
                "path",
                "state"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "available",
          "bound",
          "total",
          "modules"
        ],
        "additionalProperties": false
      },
      "errors": [
        "PreflightError",
        "source-unavailable",
        "workspace-config-invalid"
      ],
      "resource_operations": [
        "git.listFiles",
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
      "access": "read",
      "operations": [
        {
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
          },
          "name": "stat"
        },
        {
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
          },
          "name": "read"
        }
      ]
    },
    {
      "name": "git",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "access": "read",
          "arguments_schema": {
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
              "status": {
                "type": "integer"
              },
              "files": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "status",
              "files"
            ],
            "additionalProperties": false
          },
          "name": "listFiles"
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 16,
    "max_model_calls": 8
  },
  "conventions": []
}
```
</details>
