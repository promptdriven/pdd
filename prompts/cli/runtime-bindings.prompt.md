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

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

Supplied inventory and prompt read observations cover inventory shape and selected reachability decisions. Git visibility, executable/write no-link identity, workspace authorization and physical safe reads remain native. Native evidence owners: test/runtime-bindings-edges.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "7690e9e55d27a5bfe0eb43fb3ef9aef0da05760cdf480fc88d9d19b598fc02ba",
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
            "type": "string",
            "description": "JSON text encoding of the discovery record. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "selected": {
            "type": "string",
            "description": "JSON text encoding of the selected tests. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
          "value": {
            "type": "string",
            "description": "JSON text encoding of the available/bound/total/modules inventory with optional runtime. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [
        "PreflightError"
      ],
      "resource_operations": [
        "files.readFileSync",
        "files.lstatSync",
        "files.openSync",
        "files.fstatSync",
        "files.readSync",
        "files.closeSync"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "files",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readFileSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing files.readFileSync dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value",
              "error"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "lstatSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing files.lstatSync dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value",
              "error"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "openSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing files.openSync dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value",
              "error"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "fstatSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing files.fstatSync dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value",
              "error"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "readSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing files.readSync dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value",
              "error"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "closeSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing files.closeSync dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value",
              "error"
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
  "conventions": [],
  "kind": "partial"
}
```
</details>
