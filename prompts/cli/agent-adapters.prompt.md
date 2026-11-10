# Own-agent adapters

`src/agent-adapters.mjs` discovers the person's installed agent CLIs and asks one chosen agent to explain or prepare a Try input. It owns subprocess restrictions, bounded context, response parsing, fill validation and plain failure states. It never executes a filled input or chooses another provider after failure. This is new behavior; other CLI behavior and the person's saved settings, model and sign-in remain unchanged.

Export asynchronous `discoverAgents({cwd,env,run,definitions})` and `askAgent({agent,definition,cwd,env,context,entries,supportsApply=false,supportsRun=false,signal,run,timeoutMs})`. Optional `run(command,args,{cwd,env,input,signal,timeoutMs,maxBytes})` is a process port returning `{code,stdout,stderr}`. Export `runAgentProcess(command,args,options)` as that default process port. It uses a direct subprocess without a shell. Discovery uses supplied private definitions, or loads them through the configuration owner. Without custom configuration its defaults are Codex, Claude and Gemini in that order. Return only metadata, each `{id,name,state,detail?}`. States are `ready`, `available`, `signed_out`, `quota`, `not_installed`, `error`. Check installation with help and authentication with cheap status commands; never spend a model call for discovery. Unsupported read-only/authentication flags yield an explanatory error rather than an unsafe invocation.

## Bounded workspace invocation

When a [workspace policy](runtime-workspace.prompt.md) is configured, `askAgent` receives that native capability as an additive `workspace` option. Only packet-supplied project context is permitted. Read-only sandbox, small stdin and disabled write tools do not bound reads. Suppress repository read/search/glob tools, automatic project/instruction discovery and every configured context injection path before starting a model process. Apply this to configured commands and all fallback invocations; a retry cannot remove a control needed for the boundary.

Current unconfigured Claude Read/Grep/Glob permissions remain unchanged. They are insufficient in bounded mode. Current Codex read-only/ignore-rules/feature settings and Gemini deny-all overlay are also not proof that all automatic context loads are disabled. Establish supported native controls per installed CLI before bounded connection. If those controls cannot establish packet-only context, return a clear local unsupported-connection error before authentication/model invocation; never claim isolation from flags alone. No new OS sandbox is promised. Preserve the person's model/authentication and existing failure/secret handling.


## Shared credential-status interpretation

Export pure module function `parseAgentAuthStatus({agent,result})`, returning `ready`, `signed_out` or `unavailable`. Both discovery and workflow readiness use this owner; neither keeps its own auth parser. Ready means credentials configured, not that a token is unexpired or a provider request would succeed. Never run a model request to prove readiness.

Require an integer process exit code and string stdout/stderr. Codex reads both streams after removing ANSI controls: exit 0 with a `Logged in` or `API key configured` marker is ready. The latter may be followed by masked key text and `Authentication is checked when you send a request.`; never expose any of that output. `Not logged in`, `Not signed in`, or a login/sign-in-required marker on exit 0 or 1 is signed_out. A negative marker by itself is signed_out, not contradictory; both an independent affirmative marker and a negative marker together are unavailable; negative markers on exit 2 or above, nonzero success text, unrelated output and malformed results are unavailable. Claude requires strict JSON stdout with Boolean loggedIn: true on exit 0 for ready, or Boolean false on exit 0 or 1 for signed_out. Strings, missing fields, banner-prefixed JSON, malformed data and nonzero success payloads are unavailable. Unknown agent kinds are unavailable.

Discovery retains its help/read-only capability gates and existing native status commands, then maps this shared result: ready/signed_out unchanged, unavailable to error. Gemini checks the read-only features described below. No raw authentication output enters metadata or messages.

The native process port classifies ENOENT conservatively with Boolean `error.executableMissing`. It is true only when the caller cwd is an existing directory and the command has no installed candidate on the exact effective search path. A missing cwd, a present executable with a missing shebang interpreter, broken symlink or an unreadable/uncertain lookup makes it false. Inspect only cwd and candidate installation metadata, never agent credential files. Both discovery and workflow readiness report missing only for true; an injected status-process error without this evidence is unavailable. This classification never invokes help, login or a model, changes PATH, or exposes paths.

For a custom definition, `kind` selects the adapter; every help/auth/version/execution command runs its `command` directly, with a fresh child-only merge of the base environment and its overrides. Do not modify process.env, fall back to a plain executable, or expose kind, command or env in discovery metadata. `askAgent` accepts the private definition from the local bridge; without one the built-in agent IDs retain their behavior. Diagnostics use the configured display name.

Each question starts a fresh process in the project directory, without resume, model overrides or configuration writes. Codex uses the person's authentication and model, an explicit read-only sandbox, never approvals and ephemeral sessions. Disable hooks, plugins, apps, browser/computer access, multi-agent and shell execution features for this invocation; pass the tested compatibility override `-c mcp_servers={}`. This avoids creating invalid transport entries through quoted per-server keys; it does not rewrite the person’s saved MCP configuration. Do not enumerate MCP servers or write per-server `.enabled=false` settings: Codex 0.160 rejects those settings for some transports. Claude safe mode preserves model/authentication while disabling customizations, hooks, plugins and MCP; permit only Read/Grep/Glob, plan permissions, no permission prompts and no session persistence. Gemini is reported missing when absent. Do not pin Gemini versions. Discovery and each Try request inspect `--help` for the invocation features `--approval-mode`, `--admin-policy`, `--extensions`, `--allowed-mcp-server-names` and `--output-format`. If one is absent, return one clear line `Gemini Try read-only mode requires <flag>; update Gemini CLI.` before a model call. A failed help command reports that Gemini Try read-only capability discovery failed. Installed versions with these features may run the adapter. It has no cheap authentication-status command: discovery returns `available`, meaning installed and sign-in is checked on the first message, never falsely `ready`. Its fresh headless invocation uses the default approval mode, not plan mode (which can switch to YOLO and route models). Give it no tools: a temporary top-precedence system-settings overlay sets `tools.core=[]`, clears `tools.discoveryCommand` and `tools.callCommand`, disables `hooksConfig.enabled`, `admin.mcp.enabled`, `admin.extensions.enabled`, `admin.skills.enabled`, `general.plan.enabled`, `general.plan.modelRouting` and automatic updates. Preserve all original system settings, model/auth fields and the original system-defaults path. Create an owner-only temporary folder and mode-0600 settings and deny-all admin-policy files, deleting them in a finally block after success, failure or cancellation. Refuse before a model call when existing system policy files would cause the CLI to ignore the added admin policy. The deny-all wildcard policy has priority 999 in admin tier and applies in every mode. Never store private configuration in the repo, logs or relay. Do not install or sign in an agent automatically.

Give the chosen agent only the bounded request from the packet owner, using supplied context and normalized entries `{entry,prompt_path,operation,input_schema}`. Full entry schemas stay local for validation; send short signatures once. Accept optional `supportsApply` and `supportsRun` (both defaultfalse) to select the compatibility wording. Project/page text and history remain untrusted data, never executable instructions. The packet owner provides the v8 Try-guide role, coverage, own-case expectations, memory and Story-order contract: answer the actual question first,1–3 short sentences, at most60words unless asked for more; no repeated summaries; specific next steps; explicit/clear-intent fills and walk-through. No model or reasoning-effort override. Total stdin is limited to24KiB, output to128KiB and a turn to120seconds by default; cancellation terminates the process group with forced termination after a short grace period. Never silently truncate a new message or structured input.

Recursively scrub secret-named fields, common token/private-key strings, and all nonempty values of secret-named environment variables (including short values) before passing context or publishing answers. Do not transmit environment variables in the prompt. The subprocess inherits normal authentication environment; it never receives runtime owner credentials deliberately added by this module. Signed-out and usage/rate-limit errors retain their plain states; missing executables map to not_installed. A failed CLI invocation shows its first nonempty error line, with ANSI/control codes and secrets removed, prefixed by the agent name and a plain failure description. Limit that diagnostic line to 500 characters. Write the complete stderr, with secrets removed (including quoted credential assignments) but line structure preserved, to the person’s `~/.pdd/runtime/agent-chat.log`, never to the relay. Create private directories and a mode-0600 regular log; refuse symlink and nonregular log/directory targets without blocking and report when logging is unavailable. Include the local log path in the error message only when writing succeeded. Do not log prompts, environment maps or successful answers. For generic errors use “Codex could not start: …” (or the chosen agent name).

Only a Codex configuration-startup error (first nonempty stderr line is a config-loading error or an explicit unknown-feature error, with no stdout) explicitly identifying an unknown `features.<name>` option permits one retry: remove that specific disabled feature override and repeat the same restricted invocation once. Preserve read-only sandbox, never approvals and the MCP compatibility override. Never retry another failure or choose another agent. This compatibility retry occurs before a model turn; do not interpret quota, sign-in or provider failures as feature incompatibility.

Successful replies must be one strict JSON object. `say` is required nonempty text. Accept only `say`, `fill`, `apply`, `criterion`, `expect`, `save`, `next`, `run` from the agent; unknown keys or invalid say reject the reply. `fill` is optional/null or exactly `{entry,input}`; input must be a complete object for a pinned known entry. Reject unresolved step-result references. Delegate validation to checkInput; refusals OR warnings make that fill invalid. `apply` is boolean and usable only with a valid fill. `criterion` is null or an ID from supplied context.criteria. `next` is null or exactly `{text,criterion}`, with nonempty text <=200characters and a known criterion/null. `expect` is null or exactly `{text,checks}`; text is nonempty <=500characters, checks has1..32 exact `{target,path,value}` records. `save` is null or exactly `{name,criterion,checks}`; name is nonempty <=100characters, criterion is known/null, and checks has1..32 exact `{target,path}` records. Targets are result/world; paths are valid JSON Pointers <=256characters; expectation values contain no step references and the serialized expectation is <=16384bytes. Expectations require a valid fill to bind; save metadata only opens a review card after phaseB and never saves. The agent cannot author next.fill or progress; the bridge supplies them.

Drop invalid optional fields independently while keeping a valid say; an invalid fill becomes null and its apply cannot survive. Do not send partial fields or invalidate a harmless explanation because its suggestion was wrong. Scrub successful say/fill/next and validate the scrubbed fill again. A process/transport/JSON/say failure still returns `{say,fill:null,error:{state,message}}` with a plain mapped state; optional-field rejection alone is not an agent-startup failure. Legacy replies with only say/fill remain accepted.

## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.

- [Agent packet](agent-packet.prompt.md), required during generation and verification: bounded stdin and v8 system/legacy wording.

- [Local agent configuration](agent-config.prompt.md), required during generation and verification: `loadAgentDefinitions` owns trusted local definitions, precedence and validation.

- [Runtime preflight](runtime-preflight.prompt.md), required during generation and verification: exported `checkInput` owns input-schema validation. Adapter rejects warnings and unresolved references because a suggested fill must be complete.

Gemini's merged admin settings may be replaced by its remote admin defaults. Do not rely on the
local admin overlay for effect suppression: CLI --extensions none independently disables extensions,
and --allowed-mcp-server-names with a fresh unpredictable nonmatching name independently prevents
MCP startup before connection. Keep tools.core empty, discovery commands empty and hooks disabled.

## Explicitly requested page execution

Optional run is boolean. Keep true only with supportsRun, supportsApply, apply:true, a
nonnull schema-valid scrubbed fill and a manual requestKind chat/own/walk. Absence of
requestKind is legacy manual chat; kind:run or any unknown kind cannot authorize it.
The agent interprets explicit current-person intent, such as run it, try it, go or do it;
ordinary explanations, fill requests and automatic results never authorize execution.
Drop unsupported/malformed run independently, preserving valid say/fill. Never launch
a program here: the page owns the funded dispatch after its own guards.

Runtime transport: `parseAgentAuthStatus({agent, result})` returns `{state}` and raises `invalid-auth-probe` when `agent` is blank; `discoverAgents({cwd, env})` returns `{agents}` and raises `invalid-discovery-cwd` when `cwd` is blank; `askAgent({agent, cwd, env, context, entries, supportsApply, supportsRun})` returns `{say, fill, apply, run, error}` and raises `invalid-agent-request` when `agent` is unknown or `cwd` is blank; and `runAgentProcess({command, args, cwd, timeoutMs, maxBytes})` returns `{code, stdout, stderr}` and raises `executable-missing` when `process.run` reports `executableMissing: true` or `command` is blank.

Bind subprocess execution through `process.run({command, args, cwd})` and scrubbed failure stderr logging (`~/.pdd/runtime/agent-chat.log`) through `log.append({path, content})`. When definitions are omitted, `discoverAgents` calls the shared `agent-config.loadAgentDefinitions` owner for normalized local configuration data; this module derives agent states from process observations. OS process-group termination, temporary mode-`0600` Gemini system-settings overlay files and descriptor-level log permissions remain native obligations (`test/agent-adapters.test.mjs`).

Runtime uses canonical JSON text to transport native environment maps, entry schemas, workspace context and arbitrary fill/check values. It decodes the values before native configuration checks and fill validation. The native API still accepts objects. When definitions are omitted, discovery calls the shared agent-config owner. The module decides states and reply fields from process observations.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "5a2cf878ae4c988e2fabeb28c22e132f82bc0f1c0059d9899056b331c0fcbc7c",
  "entries": [
    {
      "operation": "parseAgentAuthStatus",
      "input_schema": {
        "type": "object",
        "properties": {
          "agent": {
            "type": "string"
          },
          "result": {
            "type": "object",
            "properties": {
              "code": {
                "type": "integer"
              },
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "string",
        "enum": [
          "ready",
          "signed_out",
          "unavailable"
        ]
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "discoverAgents",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "string"
          },
          "definitions": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "name": {
                  "type": "string"
                },
                "kind": {
                  "type": "string",
                  "enum": [
                    "codex",
                    "claude",
                    "gemini"
                  ]
                },
                "command": {
                  "type": "string"
                },
                "env": {
                  "type": "string"
                }
              },
              "required": [
                "id",
                "name",
                "kind",
                "command"
              ],
              "additionalProperties": false
            }
          },
          "workspace": {
            "type": "string"
          }
        },
        "required": [],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "agents": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "name": {
                  "type": "string"
                },
                "state": {
                  "type": "string",
                  "enum": [
                    "ready",
                    "available",
                    "signed_out",
                    "quota",
                    "not_installed",
                    "error"
                  ]
                },
                "detail": {
                  "type": "string"
                }
              },
              "required": [
                "id",
                "name",
                "state"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "agents"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "process.run"
      ]
    },
    {
      "operation": "askAgent",
      "input_schema": {
        "type": "object",
        "properties": {
          "agent": {
            "type": "string"
          },
          "definition": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              },
              "name": {
                "type": "string"
              },
              "kind": {
                "type": "string",
                "enum": [
                  "codex",
                  "claude",
                  "gemini"
                ]
              },
              "command": {
                "type": "string"
              },
              "env": {
                "type": "string"
              }
            },
            "required": [
              "id",
              "name",
              "kind",
              "command"
            ],
            "additionalProperties": false
          },
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "string"
          },
          "context": {
            "type": "string"
          },
          "entries": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "entry": {
                  "type": "string"
                },
                "prompt_path": {
                  "type": "string"
                },
                "operation": {
                  "type": "string"
                },
                "input_schema": {
                  "type": "string"
                },
                "result_schema": {
                  "type": "string"
                },
                "errors": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                }
              },
              "required": [
                "entry",
                "prompt_path",
                "operation",
                "input_schema",
                "result_schema"
              ],
              "additionalProperties": false
            }
          },
          "supportsApply": {
            "type": "boolean"
          },
          "supportsRun": {
            "type": "boolean"
          },
          "workspace": {
            "type": "string"
          },
          "timeoutMs": {
            "type": "integer"
          }
        },
        "required": [],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "say": {
            "type": "string"
          },
          "fill": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "entry": {
                    "type": "string"
                  },
                  "input": {
                    "type": "string"
                  }
                },
                "required": [
                  "entry",
                  "input"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "apply": {
            "type": "boolean"
          },
          "run": {
            "type": "boolean"
          },
          "criterion": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "expect": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "text": {
                    "type": "string"
                  },
                  "checks": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "path": {
                          "type": "string"
                        },
                        "target": {
                          "type": "string",
                          "enum": [
                            "result",
                            "world"
                          ]
                        },
                        "value": {
                          "type": "string"
                        }
                      },
                      "required": [
                        "path",
                        "target",
                        "value"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "text",
                  "checks"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "save": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "name": {
                    "type": "string"
                  },
                  "criterion": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "checks": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "path": {
                          "type": "string"
                        },
                        "target": {
                          "type": "string",
                          "enum": [
                            "result",
                            "world"
                          ]
                        }
                      },
                      "required": [
                        "path",
                        "target"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "name",
                  "criterion",
                  "checks"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "next": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "criterion": {
                    "oneOf": [
                      {
                        "type": "string"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "text": {
                    "type": "string"
                  }
                },
                "required": [
                  "criterion",
                  "text"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "error": {
            "type": "object",
            "properties": {
              "state": {
                "type": "string",
                "enum": [
                  "error",
                  "signed_out",
                  "quota",
                  "not_installed"
                ]
              },
              "message": {
                "type": "string"
              }
            },
            "required": [
              "state",
              "message"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "say",
          "fill"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "process.run",
        "log.append"
      ]
    },
    {
      "operation": "runAgentProcess",
      "input_schema": {
        "type": "object",
        "properties": {
          "command": {
            "type": "string"
          },
          "args": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "string"
          },
          "timeoutMs": {
            "type": "integer"
          },
          "maxBytes": {
            "type": "integer"
          }
        },
        "required": [
          "command",
          "args",
          "cwd"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "code": {
            "type": "integer"
          },
          "stdout": {
            "type": "string"
          },
          "stderr": {
            "type": "string"
          }
        },
        "required": [
          "code",
          "stdout",
          "stderr"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "process.run"
      ]
    }
  ],
  "calls": [
    {
      "operation": "discoverAgents",
      "target": "prompts/cli/agent-config.prompt.md",
      "target_operation": "loadAgentDefinitions",
      "max_calls": 1
    }
  ],
  "resources": [
    {
      "name": "process",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "run",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "command": {
                "type": "string"
              },
              "args": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "cwd": {
                "type": "string"
              },
              "env": {
                "type": "string"
              },
              "input": {
                "type": "string"
              },
              "timeoutMs": {
                "type": "integer"
              },
              "maxBytes": {
                "type": "integer"
              }
            },
            "required": [
              "command",
              "args",
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "code": {
                "type": "integer"
              },
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              },
              "executableMissing": {
                "type": "boolean"
              }
            },
            "required": [
              "code",
              "stdout",
              "stderr",
              "executableMissing"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "log",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "append",
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
            "properties": {
              "ok": {
                "type": "boolean"
              }
            },
            "required": [
              "ok"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 32,
    "max_model_calls": 16
  },
  "conventions": [
    {
      "path": "/entries/1/input_schema/properties/definitions/items/properties/env",
      "convention": "json"
    },
    {
      "path": "/entries/2/input_schema/properties/env",
      "convention": "json"
    },
    {
      "path": "/entries/2/input_schema/properties/context",
      "convention": "json"
    },
    {
      "path": "/entries/2/input_schema/properties/entries/items/properties/input_schema",
      "convention": "json"
    },
    {
      "path": "/entries/2/input_schema/properties/entries/items/properties/result_schema",
      "convention": "json"
    },
    {
      "path": "/entries/2/input_schema/properties/definition/properties/env",
      "convention": "json"
    },
    {
      "path": "/entries/2/input_schema/properties/workspace",
      "convention": "json"
    },
    {
      "path": "/entries/2/result_schema/properties/fill/oneOf/0/properties/input",
      "convention": "json"
    },
    {
      "path": "/entries/2/result_schema/properties/expect/oneOf/0/properties/checks/items/properties/value",
      "convention": "json"
    },
    {
      "path": "/entries/3/input_schema/properties/env",
      "convention": "json"
    },
    {
      "path": "/resources/0/operations/0/arguments_schema/properties/env",
      "convention": "json"
    }
  ]
}```
</details>
