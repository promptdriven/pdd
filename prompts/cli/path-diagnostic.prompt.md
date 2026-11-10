# Explain which pdd PATH selects

Own `src/path-diagnostic.mjs`, exporting `pathDiagnostic({packageRoot, cwd, env, mode})`, which returns diagnostic lines without writing files or changing installations. Help a person running this pdd by an absolute path understand why a plain `pdd` can run a different program. Preserve the CLI's version-only stdout and ordinary command results.

Read this package's version and executable identity locally. Discover executable `pdd` paths in order with `which -a pdd`; if `which` is unavailable, enumerate executable files in PATH with the same relative/empty-directory semantics. Deduplicate repeated paths; recognize symlinks to this pdd executable as the same program. Do not mistake a missing, nonexecutable or broken file for a candidate. A missing package/executable supplies no diagnostic.

When setup requests the full report, identify this running pdd executable and version, list the PATH candidates in order, and identify the first candidate and its version. If it is this pdd, use the known version. Otherwise probe only that selected executable with `--version`, never with setup or an operational command. Bound the probe to two seconds and 64 KiB; a nonzero exit, timeout, inaccessible or empty version reports version unavailable without suppressing the path or disrupting the command. Use a private environment recursion guard so probing another copy of this pdd does not launch another diagnostic. Sanitize child text to one readable line; never echo child stderr, environment values or raw errors.

For a conflict (the selected executable differs, or another distinct pdd is present), explain that a later environment activation, such as conda, can reorder PATH and shadow this pdd again. Give the verified absolute Node-plus-pdd command. If a verified executable named `pdd` on PATH points to this pdd, also give its bin-directory PATH correction, applied **after** environment activation, plus `hash -r`. Never suggest a PATH directory that lacks this pdd's command named `pdd`. Do not remove or replace another install, change PATH, ask a removal question, or run a package manager.

`mode: 'workflow'` returns only a one-line shadowing warning for workflow startup, including the selected path/version and a short `"$PDD_BIN"` hint for workflow chats; no warning when PATH selects this pdd. `mode: 'version'` emits the full report only for a conflict. `mode: 'setup'` emits the report even without a conflict. Diagnostics remain local: no runtime, authentication or agent calls.

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring. The [CLI](pdd-cli.prompt.md) owns dispatch and output streams.
- In Runtime checks, `files.stat({path})` and `files.read({path})` read `<packageRoot>/package.json`, `host.realpath({path})` returns `{exists, executable, realpath}` for `<packageRoot>/bin/pdd.mjs` and candidate paths, `host.whichPdd({cwd, pathEnv})` returns `{status, stdout}` from `which -a pdd`, and `host.probeVersion({command, cwd})` returns `{status, stdout, timedOut}` for `<selected> --version`. `pathDiagnostic({packageRoot, cwd, env, mode, execPath})` returns `{lines}` and fails with `invalid_path_diagnostic_mode` when `mode` is not `setup`, `version` or `workflow`. Real child-process timeouts, filesystem mode bits and symlink loops stay in `test/path-diagnostic.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "8698d43ecd4c355641ad88e8c97897006e93aa0d347bda3fa83601a3d8535de4",
  "entries": [
    {
      "operation": "pathDiagnostic",
      "input_schema": {
        "type": "object",
        "properties": {
          "packageRoot": {
            "type": "string"
          },
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "object",
            "properties": {
              "PATH": {
                "type": "string"
              },
              "PDD_PATH_DIAGNOSTIC_PROBE": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "mode": {
            "type": "string"
          },
          "execPath": {
            "type": "string"
          }
        },
        "required": [
          "packageRoot",
          "cwd",
          "env",
          "mode"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "lines": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "lines"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_path_diagnostic_mode"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "host.realpath",
        "host.whichPdd",
        "host.probeVersion",
        "compute.hash_utf8"
      ]
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
      "name": "host",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "realpath",
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
              "executable": {
                "type": "boolean"
              },
              "realpath": {
                "type": "string"
              }
            },
            "required": [
              "exists",
              "executable",
              "realpath"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "whichPdd",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "pathEnv": {
                "type": "string"
              }
            },
            "required": [
              "cwd",
              "pathEnv"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "status": {
                "type": "integer"
              },
              "stdout": {
                "type": "string"
              }
            },
            "required": [
              "status",
              "stdout"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "probeVersion",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "command": {
                "type": "string"
              },
              "cwd": {
                "type": "string"
              }
            },
            "required": [
              "command",
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
              "stdout": {
                "type": "string"
              },
              "timedOut": {
                "type": "boolean"
              }
            },
            "required": [
              "status",
              "stdout",
              "timedOut"
            ],
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
