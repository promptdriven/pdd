# SVG layout lint

Own `src/svg-layout.mjs`. Its module function `lintSvgLayouts({root, files, promptPaths})` returns a deterministic array of warning strings for disagreements between screen prompts and their linked `.ui.svg` drawings. It reads local files only, makes no AI or network call and changes no file. Preserve existing Check admission: these warnings never refuse a test or approve a prompt.

`root` is the repository root; `files` is its Git-visible repository-relative file list. With `promptPaths`, inspect those prompts only; without it, inspect every Git-visible `*.prompt.md`. Read local inline and reference-style Markdown image/link destinations ending in `.ui.svg`, relative to their prompt; ignore remote links, fragments and duplicate destinations. Files must stay inside root and be regular files with no symlink ancestors. An unreadable, missing, escaping or malformed drawing produces a warning naming the prompt and drawing; never silently claim it matches.

## Workspace advice

Use the [workspace authority](runtime-workspace.prompt.md) before prompt/drawing content access, including no-Story local scans. Filter optional excluded candidates without opening them; report unavailable advice where relevant. Required linked drawings remain preflight's capture responsibility and cannot be silently pruned. Keep advisory warnings advisory and retain strict no-link reads.


## Parts and advice

The drawing is the layout spec for its declared state: visible parts, words, order and stable ids. Prose owns behavior and dynamic value sources. Ignore Runtime interface JSON, valid comments and SVG `title`, `desc`, `defs`, hidden elements and their descendants. A context-only region, marked `data-context-only="true"` or class `context-only`, and its descendants are outside the owned layout. Decode XML entities and normalize whitespace and case when comparing labels; preserve original spelling in diagnostics. Reject malformed or nested comments with a source/drawing warning; never remove delimiters and reinterpret the result as active markup. CDATA remains literal SVG text. Do not execute SVG scripts or load external resources.

Report all three kinds of disagreement, identifying the prompt, drawing and part:

| Warning | Required observation |
|---|---|
| Prompt control absent from drawing | A control explicitly named by id, quoted label, or a directional-control phrase (including four direction buttons) lacks a matching visible drawing part. For directional controls name each missing direction or the missing group. |
| Drawing label absent from prompt | A visible nonnumeric label is never mentioned in the prompt prose. Match complete normalized words/phrases, not arbitrary substrings. Pure numeric sample values remain dynamic content for this advisory. |
| Drawing region layout unspecified | A visible stable id is not acknowledged as an id/region or named layout part in the prose. Generic data-field mentions do not specify that field's box, bar or container. A label such as SCORE with data prose saying “score” may match as text while the `score` region still needs a layout declaration. |

Explicit prose such as `region score`, `id="score"`, or “score box” acknowledges the corresponding named region. A backticked id within `## Appearance` also acknowledges it. Do not count an interface schema property or a general state-field declaration as a layout mapping. Retain explicit behavioral control-id declarations anywhere in the prose. Matching is conservative local advice: name uncertain/unmatched parts; do not infer a semantic equivalence or change the prompt/drawing automatically. Report source-read/parse limitations as warnings. This is a vocabulary and part check, not an AI assessment of meaning or a geometry check.

Warnings start `Warning: SVG layout`, are deduplicated and ordered by prompt path, drawing path and part. A 2048-like screen with four direction buttons only in prose and SCORE/SEED boxes and a READY bar only in the drawing must warn about directions, READY and the unspecified score/seed layout regions, even when prose mentions score and seed data.

## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.

- [Screen rules](../../RUNBOOK.md#13-give-your-app-a-screen-app-map): authoring and verification context.

## Caller navigation

The CLI exposes this advisory through [Check](runtime-client.prompt.md).

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

The files resource binds read-only Node filesystem observations used for warnings. Physical safe no-link/workspace reads and actual rendered geometry remain native. Warnings remain advice, not admission. Native evidence owners: test/svg-layout.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "54580067beadb16d2af001d18232c9e8274abde9e9badd07a8f80bfb86cd49b8",
  "entries": [
    {
      "operation": "lintSvgLayouts",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          },
          "files": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "promptPaths": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "root",
          "files"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "warnings": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "warnings"
        ],
        "additionalProperties": false
      },
      "errors": [],
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
