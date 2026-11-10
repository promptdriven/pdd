# Named local agents

`src/agent-config.mjs` owns the local list of the person's agent launchers. Export synchronous `loadAgentDefinitions({cwd,env=process.env})`, returning fresh records `{id,name,kind,command,env}`. `env` contains only overrides; the adapter merges these into the child environment. Register secret-named override values in the shared memory-only inventory after expansion, so credentials passed to children can be redacted regardless of which caller loads definitions. This interface does not execute commands, change settings or transmit configuration to the server.

Read launchers only from `$HOME/.config/pdd/agents.json`. Without HOME or that user file, return built-in defaults. Never inspect or load repository `.pdd/agents.json`, regardless of its validity, type or contents: project text must not choose a local executable or child environment. `cwd` remains an accepted argument but does not affect configuration selection. A selected invalid user file fails without fallback. A user file must be regular, not a symlink, and at most 65536 bytes. User configuration directory symlinks are permitted, supporting user-managed config directories. Read the selected file without following a final symlink and verify the byte bound on the actual read.

The JSON root is an object containing `agents` (required array, at most 24 entries) and optional boolean `include_defaults`; reject other properties. Each entry has exactly `name`, `kind`, `command`, and optional `env`. Names are nonempty, trimmed, unique, at most 100 characters and contain no controls. Kinds are `codex`, `claude`, `gemini`. Commands are nonempty strings, at most 4096 characters and contain no controls; spaces are literal executable-path characters, never shell syntax. Environment overrides are objects with at most 64 keys matching `[A-Za-z_][A-Za-z0-9_]*`; values are strings at most 8192 characters without NUL. Never interpolate variables or evaluate strings.

Expand leading `~` or `~/` in commands and environment values using the supplied HOME; other tildes remain literal. Refuse tilde expansion when HOME is unavailable. Relative command paths containing a slash resolve against the selected config directory, while program names remain PATH lookups. Absolute paths remain paths. Reject duplicate names, including collisions with enabled default display names or their lowercase IDs. Custom IDs are `custom-` followed by the first 24 lowercase hex characters of SHA-256 of the exact name; stable names retain IDs across reorderings and launcher edits.

Append defaults unless `include_defaults` is false: `{id:'codex',name:'Codex',kind:'codex',command:'codex',env:{}}`, then corresponding `claude`/`Claude` and `gemini`/`Gemini` records. An empty list with defaults disabled is valid. Invalid, unreadable or oversized files throw plain errors identifying the configuration problem, including unknown kind or missing command, without quoting file contents, command text, names or environment values. No fallback on a selected-file failure.

## Dependencies

Node built-in filesystem, path and crypto modules provide local bounded reads, path resolution and stable hashes. No project or provider dependency is required.
- [Secret redaction](secret-redaction.prompt.md) supplies secret-name selection and memory-only credential registration for expanded environment overrides.

Runtime transport: `loadAgentDefinitions({cwd, env})` returns `{definitions}` and raises `invalid-agents-config` on a symlinked, oversized, unreadable or malformed `$HOME/.config/pdd/agents.json`, tilde expansion without `HOME`, unknown `kind`, missing/invalid `command` or `env`, or duplicate/default-colliding names, without falling back to defaults.

Bind `$HOME/.config/pdd/agents.json` inspection and reads through `files.stat` and `files.read`, custom-agent SHA-256 ID derivation through `compute.hash_utf8`, and secret-named expanded override registration through `secrets.remember({values})` (`values` is the list of nonblank expanded override values whose variable names are secret-named, such as `*_KEY`, `*_TOKEN`, `*_SECRET`; omit the call when no secret-named override is present). Descriptor-level `O_NOFOLLOW` open identity and OS permissions remain native obligations (`test/agent-config.test.mjs`).

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "3f4db86460f84bcd01d8fdd71ebe0bb259ee065bbb7a8d76705cefd0c0987116",
  "entries": [
    {
      "operation": "loadAgentDefinitions",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": { "type": "string" },
          "env": {
            "type": "object",
            "properties": {
              "HOME": { "type": "string" }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": ["cwd", "env"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "definitions": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": { "type": "string" },
                "name": { "type": "string" },
                "kind": { "type": "string", "enum": ["codex", "claude", "gemini"] },
                "command": { "type": "string" },
                "env": {
                  "type": "object",
                  "properties": {
                    "OPENAI_API_KEY": { "type": "string" },
                    "CODEX_HOME": { "type": "string" },
                    "CUSTOM_PATH": { "type": "string" }
                  },
                  "required": [],
                  "additionalProperties": false
                }
              },
              "required": ["id", "name", "kind", "command", "env"],
              "additionalProperties": false
            }
          }
        },
        "required": ["definitions"],
        "additionalProperties": false
      },
      "errors": ["invalid-agents-config"],
      "resource_operations": [
        "files.stat",
        "files.read",
        "compute.hash_utf8",
        "secrets.remember"
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
          "name": "stat",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" }
            },
            "required": ["path"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exists": { "type": "boolean" },
              "size": { "type": "integer", "minimum": 0 },
              "is_symlink": { "type": "boolean" }
            },
            "required": ["exists", "size", "is_symlink"],
            "additionalProperties": false
          }
        },
        {
          "name": "read",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" }
            },
            "required": ["path"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": { "type": "string" }
            },
            "required": ["content"],
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
              "text": { "type": "string" }
            },
            "required": ["text"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": { "type": "string" }
            },
            "required": ["value"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "secrets",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "remember",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "values": {
                "type": "array",
                "items": { "type": "string" }
              }
            },
            "required": ["values"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" }
            },
            "required": ["ok"],
            "additionalProperties": false
          }
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
