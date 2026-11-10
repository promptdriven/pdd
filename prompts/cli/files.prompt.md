# Authored files view

Own `src/project-files.mjs`. Export `inspectProjectFiles(root)` and
`runProjectFiles({cwd=process.cwd(),json=false}, ports={})`.
A person can see which prompts, Stories and tests PDD reads and why it refuses
a file, without changing files, signing in or calling the interpreter.

Use the required shared reader for discovery, prompt parsing, contract expansion,
call closure, schema checks and scenario preflight. Inspect all eligible
Git-visible prompts, including prompts with no interface. Use default all-Story
fixture-project exclusions, with the same workspace limits. Report each bad
prompt or test separately and continue inspecting independent files. Reference
or source failures retain their code and reason; never print source contents.
Pair tests with Stories by the shared name rule, never by trusting story_path.
Pair prompts with tests through step entry_path, declared entry_paths and
transitive interface call targets. Keep paths sorted and unique. Do not guess
an interface kind; this task does not add or validate kind metadata.

`inspectProjectFiles` returns exactly this top-level JSON shape:
- `schema_version`: `pdd.files.v1`.
- `prompts`: path-sorted rows with `path`, `has_interface` (true for exactly one recognized
  block, false for none/multiple, null when a source/reference failure stops reading), `stories` and `tests` (sorted path arrays), `references` (the resolver's
  provenance rows), and `refusals` (the shared prompt hash/status and parse/schema
  problems, without duplicates).
- `stories`: path-sorted rows with `path`, `title` (string or null), and `tests`
  (all matching test paths, empty when untested).
- `tests`: path-sorted rows with `path`, `files` (all conflict members), `stories`
  (name-rule owners), `prompts` (entry/call closure paths), and `refusals` from
  shared scenario preflight. A source/reference failure is a refusal for that
  test and does not hide other tests.
- `orphans`: shared discovery rows `{path,line}` for test-folder JSON files with
  no Story. Do not parse these unrelated JSON files.
- `refusals`: deduplicated problems from prompt and test rows, each with `path`
  (the affected file), `code`, `section`, `message`, and any shared `hint`.
- `warnings`: shared discovery and preflight warnings, including untested Stories
  and excluded fixture projects.

A caught source/reference failure uses its code (or `source-unreadable` when
absent), section `source`, its safe message and the affected path. Sort global
refusals by path, code, section, then message. No timestamp or absolute repository
path belongs in this JSON. An empty repository returns empty arrays.

Resolve cwd's Git root with a read-only Git command. Outside Git, write one
finite stderr diagnostic and return 2. A root discovery/configuration failure
writes its reason to stderr and returns its exit code (default 4). Otherwise
print JSON plus newline with --json, or a text list of every prompt, Story, test,
orphan, refusal reason and warning. Text states whether a prompt has a Runtime
interface. Inspection returns 0 even when listed files have refusals; this is
an inventory, not a pass verdict. Use injected stdout/stderr ports for output.

## Dependencies

- [Shared authored-file reader](runtime-preflight.prompt.md): required generation,
  verification and testing context for all parsing, pairing and refusal rules.
- In Runtime checks, `git.topLevel({cwd})` and `git.listFiles({root})` supply the repository root and Git-visible relative paths (a nonzero `git.listFiles` status raises `source-unavailable`), `files.stat({path})` and `files.read({path})` read blobs under `<root>/<path>`, and `output.stdout({text})` and `output.stderr({text})` receive CLI output while `runProjectFiles` returns `{exitCode}`. Real Git subprocesses, symlink races and native filesystem permissions stay in `test/cli.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "87db4ba934faf7eb1df3b60740e70912c741486169206e587d1cf48ad5b0b825",
  "entries": [
    {
      "operation": "inspectProjectFiles",
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
          "schema_version": {
            "type": "string",
            "const": "pdd.files.v1"
          },
          "prompts": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": {
                  "type": "string"
                },
                "has_interface": {
                  "oneOf": [
                    {
                      "type": "boolean"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "stories": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "tests": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "references": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "consumer": {
                        "type": "string"
                      },
                      "source_pointer": {
                        "type": "string"
                      },
                      "target": {
                        "type": "string"
                      },
                      "kind": {
                        "type": "string",
                        "enum": [
                          "contract",
                          "seed"
                        ]
                      },
                      "value_json": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "consumer",
                      "source_pointer",
                      "target",
                      "kind",
                      "value_json"
                    ],
                    "additionalProperties": false
                  }
                },
                "refusals": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "path": {
                        "type": "string"
                      },
                      "code": {
                        "type": "string"
                      },
                      "section": {
                        "type": "string"
                      },
                      "message": {
                        "type": "string"
                      },
                      "hint": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "path",
                      "code",
                      "section",
                      "message"
                    ],
                    "additionalProperties": false
                  }
                }
              },
              "required": [
                "path",
                "has_interface",
                "stories",
                "tests",
                "references",
                "refusals"
              ],
              "additionalProperties": false
            }
          },
          "stories": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": {
                  "type": "string"
                },
                "title": {
                  "oneOf": [
                    {
                      "type": "string"
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "tests": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                }
              },
              "required": [
                "path",
                "title",
                "tests"
              ],
              "additionalProperties": false
            }
          },
          "tests": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": {
                  "type": "string"
                },
                "files": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "stories": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "prompts": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "refusals": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "path": {
                        "type": "string"
                      },
                      "code": {
                        "type": "string"
                      },
                      "section": {
                        "type": "string"
                      },
                      "message": {
                        "type": "string"
                      },
                      "hint": {
                        "type": "string"
                      },
                      "step": {
                        "type": "integer"
                      }
                    },
                    "required": [
                      "path",
                      "code",
                      "section",
                      "message"
                    ],
                    "additionalProperties": false
                  }
                }
              },
              "required": [
                "path",
                "files",
                "stories",
                "prompts",
                "refusals"
              ],
              "additionalProperties": false
            }
          },
          "orphans": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": {
                  "type": "string"
                },
                "line": {
                  "type": "string"
                }
              },
              "required": [
                "path",
                "line"
              ],
              "additionalProperties": false
            }
          },
          "refusals": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": {
                  "type": "string"
                },
                "code": {
                  "type": "string"
                },
                "section": {
                  "type": "string"
                },
                "message": {
                  "type": "string"
                },
                "hint": {
                  "type": "string"
                },
                "step": {
                  "type": "integer"
                }
              },
              "required": [
                "path",
                "code",
                "section",
                "message"
              ],
              "additionalProperties": false
            }
          },
          "warnings": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "schema_version",
          "prompts",
          "stories",
          "tests",
          "orphans",
          "refusals",
          "warnings"
        ],
        "additionalProperties": false
      },
      "errors": [
        "source-unavailable",
        "workspace-config-invalid"
      ],
      "resource_operations": [
        "git.listFiles",
        "files.stat",
        "files.read"
      ]
    },
    {
      "operation": "runProjectFiles",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "json": {
            "type": "boolean"
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
          "exitCode": {
            "type": "integer"
          }
        },
        "required": [
          "exitCode"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "git.topLevel",
        "git.listFiles",
        "files.stat",
        "files.read",
        "output.stdout",
        "output.stderr"
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
    },
    {
      "name": "git",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "topLevel",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
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
              "status": {
                "type": "integer"
              },
              "root": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              }
            },
            "required": [
              "status",
              "root",
              "stderr"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "listFiles",
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
          }
        }
      ]
    },
    {
      "name": "output",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "stdout",
          "access": "write",
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
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        },
        {
          "name": "stderr",
          "access": "write",
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
