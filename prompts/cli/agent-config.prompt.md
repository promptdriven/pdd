# Named local agents

`src/agent-config.mjs` owns the local list of the person's agent launchers. Export synchronous `loadAgentDefinitions({cwd,env=process.env})`, returning fresh records `{id,name,kind,command,env}`. `env` contains only overrides; the adapter merges these into the child environment. Register secret-named override values in the shared memory-only inventory after expansion, so credentials passed to children can be redacted regardless of which caller loads definitions. This interface does not execute commands, change settings or transmit configuration to the server.

Read launchers only from `$HOME/.config/pdd/agents.json`. Without HOME or that user file, return built-in defaults. Never inspect or load repository `.pdd/agents.json`, regardless of its validity, type or contents: project text must not choose a local executable or child environment. `cwd` remains an accepted argument but does not affect configuration selection. A selected invalid user file fails without fallback. A user file must be regular, not a symlink, and at most 65536 bytes. User configuration directory symlinks are permitted, supporting user-managed config directories. Read the selected file without following a final symlink and verify the byte bound on the actual read.

The JSON root is an object containing `agents` (required array, at most 24 entries) and optional boolean `include_defaults`; reject other properties. Each entry has exactly `name`, `kind`, `command`, and optional `env`. Names are nonempty, trimmed, unique, at most 100 characters and contain no controls. Kinds are `codex`, `claude`, `gemini`. Commands are nonempty strings, at most 4096 characters and contain no controls; spaces are literal executable-path characters, never shell syntax. Environment overrides are objects with at most 64 keys matching `[A-Za-z_][A-Za-z0-9_]*`; values are strings at most 8192 characters without NUL. Never interpolate variables or evaluate strings.

Expand leading `~` or `~/` in commands and environment values using the supplied HOME; other tildes remain literal. Refuse tilde expansion when HOME is unavailable. Relative command paths containing a slash resolve against the selected config directory, while program names remain PATH lookups. Absolute paths remain paths. Reject duplicate names, including collisions with enabled default display names or their lowercase IDs. Custom IDs are `custom-` followed by the first 24 lowercase hex characters of SHA-256 of the exact name; stable names retain IDs across reorderings and launcher edits.

Append defaults unless `include_defaults` is false: `{id:'codex',name:'Codex',kind:'codex',command:'codex',env:{}}`, then corresponding `claude`/`Claude` and `gemini`/`Gemini` records. An empty list with defaults disabled is valid. Invalid, unreadable or oversized files throw plain errors identifying the configuration problem, including unknown kind or missing command, without quoting file contents, command text, names or environment values. No fallback on a selected-file failure.

## Dependencies

Node built-in filesystem, path and crypto modules provide local bounded reads, path resolution and stable hashes. No project or provider dependency is required.
- [Secret redaction](secret-redaction.prompt.md) supplies secret-name selection and memory-only credential registration for expanded environment overrides.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

Bind the existing Node filesystem dependency through files and SHA-256 through compute.hash_utf8. The simulated reply covers configuration validation and stable IDs. Final-symlink refusal, no-follow open identity, permissions, environment credential registration and installed executable selection remain native. Native evidence owners: test/agent-config.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "a480842a531bdbb481e94d28e79325428e7bc1a645905333731779912fe66180",
  "entries": [
    {
      "operation": "loadAgentDefinitions",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "string",
            "description": "JSON text encoding of the supplied environment overrides and HOME. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
          "value": {
            "type": "string",
            "description": "JSON text encoding of the fresh id/name/kind/command/env definition records. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
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
        "files.closeSync",
        "compute.hash_utf8"
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
    },
    {
      "name": "compute",
      "kind": "compute",
      "access": "read",
      "operations": [
        {
          "name": "hash_utf8",
          "access": "read",
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
            "properties": {
              "sha256": {
                "type": "string"
              }
            },
            "required": [
              "sha256"
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
