# Shared secret redaction

Own `src/secret-redaction.mjs`. Export `redactSecrets(value, secrets = [])`,
returning a diagnostic string. The validation threat model covers what the child
can print: every nonempty secret-named value in its own environment and every
credential pdd passes to it in arguments, handed-over files or agent-definition
environment overrides. Register those overrides when loading agent definitions,
before they can reach a child. Credentials held only in other processes, such as
an alert bot token that the validation child cannot read, are outside this
completeness guarantee. Collect values from environment
names containing TOKEN, SECRET, PASSWORD, PASSWD, CREDENTIAL, AUTHORIZATION or
COOKIE, names ending in _KEY, and API key names (including GH_TOKEN,
GITHUB_TOKEN and OPENAI_API_KEY). Include explicit caller secrets and gh and
agent credentials read by pdd. Remember these credentials only in memory;
never save the value inventory or include it in child command arguments.
Export `rememberSecrets(...values)` to register read credentials and
`knownSecretValues(env = process.env, secrets = [])` to obtain the deduplicated
inventory, including process environment values and explicit invocation values.
Replace exact values with `[redacted]` before pattern matching or truncation.
For both scalar and stream text, scan original input from left to right. At each
position choose the longest known matching value, consume it in full and resume
after it. Registration order must not expose the tail of a longer match. Do not
rescan replacement text. Preserve unmatched text, including the unmatched tail
of a value that starts inside an already consumed match.

Export `redactingValues(emit, secrets)` with write(text) and end() methods.
It redacts exact values on each independent string stream, using a bounded
overlap window derived from the longest known value. Transport chunks and line
breaks do not end that window. A value containing line breaks is matched as
supplied, without normalization. Scan before discarding oversized lines. Do not
emit an undecided prefix of a known value. At EOF redact complete matches and
release safe remaining text. Call emit(text, original) with strings: text is
safe output and original is the consumed input for internal byte accounting.
Original can contain a secret; never store or forward it. A caller can use
lossless byte strings when it encodes secret values the same way. Preserve
ordinary text and recover after a match.

Pattern redaction is a best-effort extra layer for unknown values, not a
complete guarantee. Reuse the agent guide's string sanitizer: remove URL
user/password and secret query values; redact PEM private keys (including
unterminated blocks), GitHub `gh[pousr]_` and `github_pat_` tokens, OpenAI `sk-`
tokens, Basic/Bearer credentials, and case-insensitive colon/equal pairs for
key, token, password, secret, api_key, authorization, cookie and credential.
Also cover Google `AIza` API keys and `ya29.` access tokens. Pairs accept quoted
or unquoted values. Redact an entire Authorization header value, including
other schemes. Basic/Bearer whitespace includes line breaks; bounded stream
recognition must retain a pending scheme across whitespace and omitted lines,
then suppress its credential through the next whitespace or EOF. Remove control
bytes except tab, CR and LF. Unknown encodings, unrecognized formats and
arbitrary positional values may evade patterns. Exact matching does not cover
transformed, encoded or altered copies of a known value. Callers must pass
newly learned values before emitting output that can contain them.

## Dependencies

- Native JavaScript strings, regular expressions and URL parsing.
- In Runtime checks, `memory.load({id})` and `memory.save({id, state})` under `id: "global"` persist the remembered `{secrets}` list across calls (`rememberSecrets({values})` raises `empty-secret-values` when `values` is empty, appends nonempty string values in insertion order without duplicates, and returns `{rememberedCount}`; `knownSecretValues({env, secrets})` raises `invalid-secret-env` when `env` is null and returns `{secrets}` combining remembered values, explicit `secrets`, and matching `env` entries in deduplicated order). `redactingValues({secrets})` is a `prompt-runtime.interface.v2` `RedactingStream` factory (raising `invalid-stream-secrets` when `secrets` is null) that stores `{secrets, pending: "", closed: false}` via `streams.store({handle, state})` under the executor-issued `instance_handle` and returns `{handle}`. Instance methods `write({handle, text})` and `end({handle})` load state via `streams.load({handle})` (raising `stream-closed` when missing or already closed), emit releasable substrings and `[redacted]` replacements via `output.emit({text, original})` while holding back `overlap = max(0, maxSecretLength - 1)` trailing characters until `end`, update state via `streams.store({handle, state})`, and return `{bufferedLength}` and `{flushed}` respectively. `redactSecrets({value, secrets})` raises `invalid-redact-target` when `value` is null and returns `{text}` after exact known-secret replacement and pattern sanitization. Native process environment access stays in `test/validation-evidence.test.mjs` and `test/validation-receipts.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "730c045cdc8e209f9683838c4c8f957419e78070bbcc2fbcb7ae96bc6aad49bc",
  "entries": [
    {
      "operation": "rememberSecrets",
      "input_schema": {
        "type": "object",
        "properties": {
          "values": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "values"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "rememberedCount": {
            "type": "integer",
            "minimum": 0
          }
        },
        "required": [
          "rememberedCount"
        ],
        "additionalProperties": false
      },
      "errors": [
        "empty-secret-values"
      ],
      "resource_operations": [
        "memory.load",
        "memory.save"
      ]
    },
    {
      "operation": "knownSecretValues",
      "input_schema": {
        "type": "object",
        "properties": {
          "env": {
            "oneOf": [
              {
                "type": "object",
                "additionalProperties": false,
                "properties": {
                  "GH_TOKEN": {
                    "type": "string"
                  },
                  "GITHUB_TOKEN": {
                    "type": "string"
                  },
                  "PDD_RUNTIME_TOKEN": {
                    "type": "string"
                  },
                  "HOME": {
                    "type": "string"
                  }
                },
                "required": []
              },
              {
                "type": "null"
              }
            ]
          },
          "secrets": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "env"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "secrets": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "secrets"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-secret-env"
      ],
      "resource_operations": [
        "memory.load"
      ]
    },
    {
      "operation": "redactingValues",
      "input_schema": {
        "type": "object",
        "properties": {
          "secrets": {
            "oneOf": [
              {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "secrets"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-stream-secrets"
      ],
      "instance": {
        "kind": "factory",
        "type": "RedactingStream",
        "path": "/handle"
      },
      "resource_operations": [
        "streams.store"
      ]
    },
    {
      "operation": "write",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "text": {
            "type": "string"
          }
        },
        "required": [
          "handle",
          "text"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "bufferedLength": {
            "type": "integer",
            "minimum": 0
          }
        },
        "required": [
          "bufferedLength"
        ],
        "additionalProperties": false
      },
      "errors": [
        "stream-closed"
      ],
      "instance": {
        "kind": "method",
        "type": "RedactingStream",
        "path": "/handle"
      },
      "resource_operations": [
        "streams.load",
        "streams.store",
        "output.emit"
      ]
    },
    {
      "operation": "end",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          }
        },
        "required": [
          "handle"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "flushed": {
            "type": "boolean"
          }
        },
        "required": [
          "flushed"
        ],
        "additionalProperties": false
      },
      "errors": [
        "stream-closed"
      ],
      "instance": {
        "kind": "method",
        "type": "RedactingStream",
        "path": "/handle"
      },
      "resource_operations": [
        "streams.load",
        "streams.store",
        "output.emit"
      ]
    },
    {
      "operation": "redactSecrets",
      "input_schema": {
        "type": "object",
        "properties": {
          "value": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "secrets": {
            "type": "array",
            "items": {
              "type": "string"
            }
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
        "invalid-redact-target"
      ],
      "resource_operations": [
        "memory.load"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "memory",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              }
            },
            "required": [
              "id"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "state": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "secrets": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      }
                    },
                    "required": [
                      "secrets"
                    ],
                    "additionalProperties": false
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "state"
            ],
            "additionalProperties": false
          },
          "name": "load"
        },
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              },
              "state": {
                "type": "object",
                "properties": {
                  "secrets": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  }
                },
                "required": [
                  "secrets"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "id",
              "state"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "state": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "state"
            ],
            "additionalProperties": false
          },
          "name": "save"
        }
      ]
    },
    {
      "name": "streams",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              },
              "state": {
                "type": "object",
                "properties": {
                  "secrets": {
                    "type": "array",
                    "items": {
                      "type": "string"
                    }
                  },
                  "pending": {
                    "type": "string"
                  },
                  "closed": {
                    "type": "boolean"
                  }
                },
                "required": [
                  "secrets",
                  "pending",
                  "closed"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "handle",
              "state"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "state": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {},
                    "required": [],
                    "additionalProperties": false
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "state"
            ],
            "additionalProperties": false
          },
          "name": "store"
        },
        {
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              }
            },
            "required": [
              "handle"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "state": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "secrets": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "pending": {
                        "type": "string"
                      },
                      "closed": {
                        "type": "boolean"
                      }
                    },
                    "required": [
                      "secrets",
                      "pending",
                      "closed"
                    ],
                    "additionalProperties": false
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "state"
            ],
            "additionalProperties": false
          },
          "name": "load"
        }
      ]
    },
    {
      "name": "output",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "text": {
                "type": "string"
              },
              "original": {
                "type": "string"
              }
            },
            "required": [
              "text",
              "original"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "name": "emit"
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 28,
    "max_model_calls": 14
  },
  "conventions": [
    {
      "path": "/entries/2/result_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/3/input_schema/properties/handle",
      "convention": "handle"
    },
    {
      "path": "/entries/4/input_schema/properties/handle",
      "convention": "handle"
    }
  ],
  "schema_version": "prompt-runtime.interface.v2",
  "instance_types": [
    {
      "name": "RedactingStream",
      "resource": "streams"
    }
  ]
}
```
</details>
