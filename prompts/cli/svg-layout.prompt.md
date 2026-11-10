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

Warnings have the exact shape `Warning: SVG layout <prompt> -> <drawing>: <part>: <reason>.` where `<part>` is `control "<control>"` (`reason`: `prompt control absent from drawing`), `label "<label>"` (`reason`: `drawing label absent from prompt`), `region #<id>` (`reason`: `drawing region layout unspecified in prompt`), `drawing` (for missing, symlink or malformed drawings; a missing file uses reason `not a regular file`), or `source` (with `<drawing>` set to `(unread)` when the prompt itself cannot be read), deduplicated and ordered by prompt path, drawing path, part and reason. A 2048-like screen with four direction buttons only in prose and SCORE/SEED boxes and a READY bar only in the drawing must warn about directions, READY and the unspecified score/seed layout regions, even when prose mentions score and seed data.

## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.
- [Screen rules](../../RUNBOOK.md#13-give-your-app-a-screen-app-map): authoring and verification context.
- In Runtime checks, `files.stat({path})` and `files.read({path})` inspect blobs under `<root>/<path>`, starting with `<root>/pdd-workspace.json` when present (raising `workspace-config-unsafe` for a symlink or oversized policy and `workspace-config-invalid` for invalid JSON or `allowed_paths`), and `lintSvgLayouts` returns `{warnings}`. Native no-link traversal and rendered geometry stay in `test/svg-layout.test.mjs`.

## Caller navigation

The CLI exposes this advisory through [Check](runtime-client.prompt.md).

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "e5d3fa68d7ebc905abbe0aa19b7a363700f5d7d2628cb254c0978154541e3967",
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
      "errors": [
        "workspace-config-invalid",
        "workspace-config-unsafe"
      ],
      "resource_operations": [
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
