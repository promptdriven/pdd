# Repository Autopilot settings

`src/autopilot.mjs` exports module function `runAutopilot(input, ports)` for setup, mode, trust, untrust and trust lookup. It owns repository Autopilot settings; the CLI dispatches to it. Preserve other `pdd.json` keys, including `strict_approvals`. The stored shape is `{"autopilot":{"mode":"off","trust":[]}}`: mode is `off`, `observe` or `auto`; trust contains explicitly added GitHub names. Missing settings mean effective off and an empty list. An invalid saved mode remains untouched on setup, reads as off and produces a one-line explanation containing the lowercase word "invalid", for example: `Saved Autopilot mode "turbo" is invalid; using off and leaving it unchanged.` Mode commands replace it. Choosing a mode starts no run or interpreter; approval policy is unchanged.

Setup in a Git repository with a terminal asks for a mode only when no Autopilot setting exists; an empty answer selects off. It displays the repository owner and available write-access collaborators or team members and asks optionally for additional names; empty adds none. If lookup is incomplete, including when neither owner nor writers are available, warn that the trusted list may be incomplete and continue. When neither is available, only explicitly added names establish trust. Outside a Git root, setup returns exit code 0 with an empty message, asks nothing and saves nothing. Without a terminal, setup asks nothing and saves nothing; effective mode is off when no setting exists. A failed write reports one clear error and nonzero exit and leaves the file unchanged.

`pdd autopilot off`, `observe`, and `auto` save the named mode. `pdd autopilot trust <name>...` adds explicit names; `pdd autopilot untrust <name>` removes an explicit name. Compare GitHub names case-insensitively, preserve the first spelling, ignore duplicates and absent removals. Owner and write-access people remain trusted independently of explicit names. An author is trusted if a supplied owner, write-access name or explicit name matches; missing lookup data never establishes trust. This lookup determines trust only; later skills own run actions.

The input action is `setup`, `mode`, `trust`, `untrust`, or `isTrusted`. For mode, `mode` is the selected value, for trust/untrust names are operands, and for isTrusted author is the issue author. `interactive` and `inRepo` describe setup context. Terminal mode and names questions, config read/save and GitHub lookup are injected ports; defaults use the actual repository, filesystem and GitHub. `config.read` reads key `autopilot` and returns its JSON text as `raw`, or null if absent; `config.save` writes JSON text as `raw` for the same key and returns it, atomically preserving other top-level keys. The adapter encodes saved values as compact JSON; it preserves unknown Autopilot keys when updating the setting. `github.lookup` supplies owner and write-access names, with `complete` false on incomplete lookup; unavailable owner is the empty string and unavailable writers are an empty list. Translate lookup failure into incomplete data; never trust an empty owner or absent data. The actual terminal ports ask separately for a mode and additional names, consuming successive input lines in order even when both answers arrive together. `terminal.mode({})` returns `{answer}`; blank selects off, and an explicit answer must be off, observe or auto. `terminal.names({owner,writers,complete})` displays these names as trusted, identifies owner and writers, asks who else to add, and returns `{names}`. The setup result message also includes the displayed names and identifies their trust and roles. On fresh setup it asks both questions. On repeat setup it does not ask for a mode or save a new mode; it saves nonempty additional names, while an empty names answer makes no save. An existing object with no mode reads as off without asking again; invalid saved values stay unchanged unless a mode command replaces them. With an existing non-object Autopilot value, trust and untrust save nothing, return exit code 0 and report that the saved value is unchanged; a mode command can replace it. A non-terminal or outside-repository setup asks neither and saves nothing. A stored invalid mode of any type reads as off with a one-line notice and remains unchanged until a mode command replaces it. Result fields report effective mode, explicit trust, author trust, a human-readable message and exit code. Inputs and results in Runtime bind this same public function and its ports; they do not invoke real Git, GitHub or disk.

Future workflow skills own run actions: in auto they record the checker’s PASS as approval words using `--said`, marked as decided by the checker; in off and observe the person approves as today. When GitHub supplies neither owner nor writers, only explicitly trusted names qualify for full auto; no other author's issue gets full auto. This does not change runtime approval enforcement or bypass strict approvals. See the [approval policy](approval-policy.prompt.md) for its independent policy.

## Dependencies

None.

Actions outside the stated set, invalid mode operands and missing or blank names return exit code 2 with a clear message and no save. Trust takes one or more nonblank names; untrust takes exactly one; isTrusted takes one nonblank author. Omitted interactive and inRepo default false. Successful actions return exit code 0, effective mode, explicit names, trusted false except for isTrusted, and a human-readable message (empty for outside-repository setup). Preserve unrelated top-level and Autopilot keys when saving; absent mode and trust read as off and empty. Failed writes return nonzero with a clear error and leave the file unchanged.

<details><summary>Runtime interface</summary>


```json
{
  "status": "approved",
  "entries": [
    {
      "operation": "runAutopilot",
      "input_schema": {
        "type": "object",
        "properties": {
          "action": {
            "type": "string"
          },
          "mode": {
            "type": "string"
          },
          "names": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "author": {
            "type": "string"
          },
          "interactive": {
            "type": "boolean"
          },
          "inRepo": {
            "type": "boolean"
          }
        },
        "required": [
          "action"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "mode": {
            "type": "string"
          },
          "trust": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "trusted": {
            "type": "boolean"
          },
          "message": {
            "type": "string"
          },
          "exitCode": {
            "type": "integer"
          }
        },
        "required": [
          "mode",
          "trust",
          "trusted",
          "message",
          "exitCode"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "config",
      "kind": "key-value",
      "access": "write",
      "operations": [
        {
          "name": "read",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "key": {
                "type": "string",
                "enum": [
                  "autopilot"
                ]
              }
            },
            "required": [
              "key"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "raw": {
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
              "raw"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "save",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "key": {
                "type": "string",
                "enum": [
                  "autopilot"
                ]
              },
              "raw": {
                "type": "string"
              }
            },
            "required": [
              "key",
              "raw"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "raw": {
                "type": "string"
              }
            },
            "required": [
              "raw"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "github",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "lookup",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "owner": {
                "type": "string"
              },
              "writers": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "complete": {
                "type": "boolean"
              }
            },
            "required": [
              "owner",
              "writers",
              "complete"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "terminal",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "mode",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "answer": {
                "type": "string"
              }
            },
            "required": [
              "answer"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "names",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "owner": {
                "type": "string"
              },
              "writers": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "complete": {
                "type": "boolean"
              }
            },
            "required": [
              "owner",
              "writers",
              "complete"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "names": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "names"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 12,
    "max_model_calls": 6
  },
  "conventions": [],
  "prose_sha256": "952cf8116a16c186e0e1e3acc588c25374b449c5a3321147c15fec3f54188e2b"
}
```
</details>
