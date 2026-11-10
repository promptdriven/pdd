# Run chat launch profiles

Own `src/workflow-launch-profile.mjs`. A launch profile selects settings for the
next chat without changing the person's account configuration. Preserve existing
agent kind, account isolation, full-access and agents.json login behavior.

`launchProfile(run, chat?)` returns a fresh profile with exactly `agent`,
`configDir` (folder or null), `model` (string or null), `herdrAgentName` (name
prefix), and `codexThreads` (integer or null). Prefer the chat's saved profile,
else the run's profile. A legacy chat without a snapshot uses its own agent and
configDir, with unset model and threads. A legacy run uses its saved fields.
Unset model and threads leave native defaults in effect. Default name prefix is
`pdd-` plus the first 12 hex SHA256 characters of repository and run identity.
`chatAgentName(profile, area, run)` appends `-` and the first six hex SHA256
characters of repository, run identity and area. Thus peer areas and independent runs have different names, while a
replacement of one area's closed chat keeps its name.

`selectLaunchProfile({run, configDir, model, herdrAgentName, codexThreads}, ports)`
merges explicitly supplied values into the run profile. Model must be a nonempty
trimmed string without controls or a leading dash. Name prefix must match
`[a-z][a-z0-9_-]{0,24}`. A requested Codex thread limit is a whole decimal number
from 4 through 8; reject it for other agents. Malformed options throw
`invalid_launch_profile` before effects. Omitted values retain saved settings.

When a Codex thread limit is selected, read only that account's `config.toml`
through `ports.profileFs` (default node:fs), using the expanded explicit folder or
`HOME/.codex`. Parse TOML with the bundled parser. Preserve a higher positive
integer `features.multi_agent_v2.max_concurrent_threads_per_session` by taking
the maximum. Missing file means no account override. Malformed TOML, invalid
configured limits, and other read errors refuse with `invalid_launch_profile`;
never include file contents or credentials in an error. Read settings only when
selecting a profile; snapshots pin the effective limit for later native effects.
Never read authentication files, sign out, reset usage or write account files.

`validLaunchProfile(value)` checks the saved shape and types; saved effective
Codex limits may exceed 8 to retain a person's higher setting. Null model and
threads represent omitted options. A profile contains no login values.

## Dependencies

- In Runtime checks, `compute.hash_utf8({text})` computes deterministic SHA-256 digests (`<repository>\n<runId>` for the 12-hex default prefix and `<repository>\n<runId>\n<area>` for the 6-hex area suffix), and `profileFs.stat({path})` and `profileFs.read({path})` inspect `<configDir>/config.toml` when selecting a Codex thread limit. `launchProfile({run, chat})` fails with `invalid_launch_profile` when the resolved `agent` is not `claude` or `codex`; `chatAgentName({profile, area, run})` fails with `invalid_launch_profile` when `area` is blank; `selectLaunchProfile({run, configDir, model, herdrAgentName, codexThreads, env})` fails with `invalid_launch_profile` on malformed options, a Codex thread limit on `claude`, or malformed `config.toml`; `validLaunchProfile({value, requireValid})` returns `{value: boolean}` and fails with `invalid_launch_profile` when `requireValid` is `true` and the profile is invalid. Native account directories and home path expansion stay in `test/workflow-launch-profile.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "4108a7d04c0fda1e087415c31a4e163b146f39d36e9ded00bee4400b9c3546b5",
  "entries": [
    {
      "operation": "launchProfile",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "repository": {
                "type": "string"
              },
              "root": {
                "type": "string"
              },
              "number": {
                "type": "integer"
              },
              "agent": {
                "type": "string"
              },
              "configDir": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "launchProfile": {
                "type": "object",
                "properties": {
                  "agent": {
                    "type": "string"
                  },
                  "configDir": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "model": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "herdrAgentName": {
                    "type": "string"
                  },
                  "codexThreads": {
                    "oneOf": [
                      {
                        "type": "integer"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  }
                },
                "required": [
                  "agent",
                  "configDir",
                  "model",
                  "herdrAgentName",
                  "codexThreads"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "runId",
              "repository",
              "agent"
            ],
            "additionalProperties": false
          },
          "chat": {
            "type": "object",
            "properties": {
              "agent": {
                "type": "string"
              },
              "configDir": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "launchProfile": {
                "type": "object",
                "properties": {
                  "agent": {
                    "type": "string"
                  },
                  "configDir": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "model": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "herdrAgentName": {
                    "type": "string"
                  },
                  "codexThreads": {
                    "oneOf": [
                      {
                        "type": "integer"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  }
                },
                "required": [
                  "agent",
                  "configDir",
                  "model",
                  "herdrAgentName",
                  "codexThreads"
                ],
                "additionalProperties": false
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "agent": {
            "type": "string"
          },
          "configDir": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "model": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "herdrAgentName": {
            "type": "string"
          },
          "codexThreads": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "agent",
          "configDir",
          "model",
          "herdrAgentName",
          "codexThreads"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_launch_profile"
      ],
      "resource_operations": [
        "compute.hash_utf8"
      ]
    },
    {
      "operation": "chatAgentName",
      "input_schema": {
        "type": "object",
        "properties": {
          "profile": {
            "type": "object",
            "properties": {
              "herdrAgentName": {
                "type": "string"
              }
            },
            "required": [
              "herdrAgentName"
            ],
            "additionalProperties": false
          },
          "area": {
            "type": "string"
          },
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "repository": {
                "type": "string"
              }
            },
            "required": [
              "runId",
              "repository"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "profile",
          "area",
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "name": {
            "type": "string"
          }
        },
        "required": [
          "name"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_launch_profile"
      ],
      "resource_operations": [
        "compute.hash_utf8"
      ]
    },
    {
      "operation": "selectLaunchProfile",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "repository": {
                "type": "string"
              },
              "agent": {
                "type": "string"
              },
              "configDir": {
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
              "repository",
              "agent"
            ],
            "additionalProperties": false
          },
          "configDir": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "model": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "herdrAgentName": {
            "type": "string"
          },
          "codexThreads": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          },
          "env": {
            "type": "object",
            "properties": {
              "HOME": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "agent": {
            "type": "string"
          },
          "configDir": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "model": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "herdrAgentName": {
            "type": "string"
          },
          "codexThreads": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "agent",
          "configDir",
          "model",
          "herdrAgentName",
          "codexThreads"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_launch_profile"
      ],
      "resource_operations": [
        "compute.hash_utf8",
        "profileFs.stat",
        "profileFs.read"
      ]
    },
    {
      "operation": "validLaunchProfile",
      "input_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "object",
            "properties": {
              "agent": {
                "type": "string"
              },
              "configDir": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "model": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "herdrAgentName": {
                "type": "string"
              },
              "codexThreads": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "agent",
              "configDir",
              "model",
              "herdrAgentName",
              "codexThreads"
            ],
            "additionalProperties": false
          },
          "requireValid": {
            "type": "boolean"
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "boolean"
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_launch_profile"
      ],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
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
              "value": {
                "type": "string"
              }
            },
            "required": [
              "value"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "profileFs",
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
