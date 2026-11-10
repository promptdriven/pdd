# Project setup

Own `src/project-setup.mjs`. Export `setupProject({cwd, packageRoot})` and `ignorePddFolder({root})`. They do what the [pdd-setup skill](../../skills/pdd-setup/SKILL.md) tells an agent to do, without an agent: `setupProject` adds or updates one short PDD block in the file that the project's agents read, and `ignorePddFolder` keeps the local `.pdd/` folder out of Git. `pdd setup` calls both.

## The block

The block is the fenced block in `<packageRoot>/skills/pdd-setup/SKILL.md`: from the line that is exactly `<!-- pdd:start -->` to the line that is exactly `<!-- pdd:end -->`. Read it from that file, so the skill and the command cannot drift apart. If the package has no `RUNBOOK.md`, leave out each block line that names `RUNBOOK.md`. If the skill has no such block, throw an error.

## Where it goes

| Project folder (`cwd`) | File |
| --- | --- |
| Has `CLAUDE.md` | `CLAUDE.md` |
| Has `AGENTS.md` and no `CLAUDE.md` | `AGENTS.md` |
| Has neither | Create `AGENTS.md` with only the block |

- The file has exactly one line `<!-- pdd:start -->` and, after it, one line `<!-- pdd:end -->`: replace those lines and the lines between them with the block. Keep all other text.
- The file has no marker line: add the block at the end, after one empty line. If the file does not end with a newline, add one first.
- Any other marker count or order: throw an error that names both markers, and write nothing.
- The file ends with a newline after the block.
- If the new text equals the old text, write nothing.

Return `{file, changed}`: the absolute file path and whether the file was written. Never paste the guide or a workflow. `setupProject` never touches another file.

## Ignore `.pdd/`

`pdd test` keeps its local cache in `.pdd/` at the Git root. That folder must never go into a commit. `ignorePddFolder({root})` gets the Git top-level folder and changes only `<root>/.gitignore`. Read the lines as Git does: drop spaces and a CR at the end of a line, and keep spaces at its start. An ignore line is `.pdd`, `.pdd/`, `/.pdd` or `/.pdd/`. A negation line is `!` and an ignore line. The last ignore or negation line counts, as in Git:

| `.gitignore` | Result |
| --- | --- |
| Does not exist | Create it with the one line `.pdd/` |
| Its last such line is an ignore line | Write nothing |
| Its last such line is a negation line | Write nothing, and return `negated: true`: the person keeps `.pdd/` in Git |
| Has no such line, but a line `!` for `.pdd` or a path in it: `!`, an optional `/` or `**/`, then `.pdd` and the line end, `/`, `*`, `?` or `[` (for example `!.pdd/config.json`) | Write nothing, and return `negated: true`: a `.pdd/` line after it would override the person's more specific rule |
| Has none of these lines | Append the line `.pdd/`. If the file does not end with a newline, append one first. Use CRLF for both when the file has a CRLF, else LF |
| Is not a regular file (a folder or a symbolic link) | Throw an error that names the file and says to add `.pdd/` by hand; write nothing |

Keep every old byte: read the file as bytes and only append. A file that is not valid UTF-8 keeps its bytes. Return `{file, changed, negated}`: the absolute `.gitignore` path, whether the file was written, and whether a negation line kept it unchanged.

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) runs it for `pdd setup`.
- In Runtime checks, `files.stat({path})`, `files.read({path})` and `files.write({path, content})` inspect and update `<packageRoot>/skills/pdd-setup/SKILL.md`, `<packageRoot>/RUNBOOK.md`, `<cwd>/CLAUDE.md`, `<cwd>/AGENTS.md` and `<root>/.gitignore`. `setupProject({cwd, packageRoot})` fails with `missing_pdd_block` when the skill file has no `<!-- pdd:start -->`...`<!-- pdd:end -->` block and `invalid_pdd_markers` when the target instruction file has an invalid marker count or order; `ignorePddFolder({root})` fails with `invalid_gitignore_target` when `<root>/.gitignore` is a symlink (`is_symlink: true`). Raw non-UTF-8 byte preservation and native directory-entry checks stay in `test/workflow-setup.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "32983fa3e6c9e8d9ac6d68bd5456f84e245ecf927d33784c0426d155fcee3fe7",
  "entries": [
    {
      "operation": "setupProject",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "packageRoot": {
            "type": "string"
          }
        },
        "required": [
          "cwd",
          "packageRoot"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "file": {
            "type": "string"
          },
          "changed": {
            "type": "boolean"
          }
        },
        "required": [
          "file",
          "changed"
        ],
        "additionalProperties": false
      },
      "errors": [
        "missing_pdd_block",
        "invalid_pdd_markers"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "files.write"
      ]
    },
    {
      "operation": "ignorePddFolder",
      "input_schema": {
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
          "file": {
            "type": "string"
          },
          "changed": {
            "type": "boolean"
          },
          "negated": {
            "type": "boolean"
          }
        },
        "required": [
          "file",
          "changed",
          "negated"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_gitignore_target"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "files.write"
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
    }
  ],
  "limits": {
    "max_steps": 24,
    "max_model_calls": 10
  },
  "conventions": []
}
```
</details>
