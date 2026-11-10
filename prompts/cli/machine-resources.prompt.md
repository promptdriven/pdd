# Machine resource observations

Own `src/machine-resources.mjs`. Export async `readMachineResources({cwd}, ports={})`.
This is the single machine observation port for health and machine-sized check
slots (#3067). It reads no credentials and makes no network or model call.
Return `{cpuCount, load, memory:{available,total}, pressure:{io,memory}, disk:{available,total}}`.
CPU count is a positive integer; load is the one-minute OS load. Memory and disk
quantities are bytes; pressure numbers are Linux PSI `some avg10` percentages.
Use Linux MemAvailable and MemTotal (convert KiB to bytes), else OS free/total
memory. Non-Linux pressure is null for each metric. Use statfs on cwd's volume,
with bavail (space available to this user) and blocks times bsize. Failed or
malformed individual observations return null for that metric; never fabricate a
healthy value. An unreadable pressure file does not hide other observations.
When `ports.includeChecks` is true, add `check:{cpuIds,platform,battery,virtualized,taskset}`.
CPU IDs are the allowed Linux affinity IDs, else available parallelism indices.
Battery detection uses Linux power-supply types. Virtualization is true only after
a successful bounded systemd-detect-virt probe; unknown reserves personal capacity.
Taskset is an executable absolute PATH selection or null. Export
`machineCheckPorts(env, ports)` as the synchronous compatibility adapters for
legacy capacity callers: cores, platform, battery, virtualized, taskset, memory
and load. They use the same native readers; policy stays with the queue.

Ports: `readFile(path)`, `statfs(path)`, `cpuCount()`, `load()`, `memory()` and
`platform`, with native Node defaults. Callers can inject `machineResources`
with the same input/output contract; policy belongs to those callers.

## Dependencies

Node `fs`, `os` and `child_process` supply the native defaults (`readFileSync`, `readdirSync`, `statfsSync`, `cpus`, `availableParallelism`, `loadavg`, `freemem`, `totalmem`, `spawnSync`). Native process and filesystem bindings stay a native obligation covered by `test/machine-resources.test.mjs`. In the Runtime interface, `readMachineResources({cwd, platform, includeChecks, env})` and `machineCheckPorts({platform, env})` use the `files` blob resource (`read`, `stat`), the `fs` port (`readdir`) and the `os` port (`cpuCount`, `load`, `memory`, `statfs`, `detectVirt`): on `platform === "linux"`, `readMachineResources` reads `/proc/meminfo`, `/proc/pressure/io`, and `/proc/pressure/memory` (and when `includeChecks` is true, `/proc/self/status` for `Cpus_allowed_list`, `fs.readdir` on `/sys/class/power_supply` plus `/sys/class/power_supply/<entry>/type` for `Battery`, `os.detectVirt({})` where `status === 0` is `true`, and `files.stat` on each `env.PATH` directory's `<dir>/taskset`), while on non-Linux it calls `os.memory({})` (`0 <= available <= total`) and sets `pressure` to `{io: null, memory: null}`; `machineCheckPorts` returns `{cores, platform, battery, virtualized, taskset, memory, load}` using `/proc/self/status` on Linux or `[0..count-1]` from `os.cpuCount({})` on non-Linux, `/sys/class/power_supply` on Linux or `battery: false` on non-Linux, `os.detectVirt({}).status === 0`, `files.stat` on `env.PATH` `<dir>/taskset`, `os.memory({}).available`, and `os.load({}).value`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "0400f2366b980d9b1a49a932d810288f181c5b3e33340ec31e1b87c67a93ad76",
  "entries": [
    {
      "operation": "readMachineResources",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "platform": {
            "type": "string"
          },
          "includeChecks": {
            "type": "boolean"
          },
          "env": {
            "type": "object",
            "properties": {
              "PATH": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
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
          "cpuCount": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          },
          "load": {
            "oneOf": [
              {
                "type": "number"
              },
              {
                "type": "null"
              }
            ]
          },
          "memory": {
            "type": "object",
            "properties": {
              "available": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "total": {
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
              "available",
              "total"
            ],
            "additionalProperties": false
          },
          "pressure": {
            "type": "object",
            "properties": {
              "io": {
                "oneOf": [
                  {
                    "type": "number"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "memory": {
                "oneOf": [
                  {
                    "type": "number"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "io",
              "memory"
            ],
            "additionalProperties": false
          },
          "disk": {
            "type": "object",
            "properties": {
              "available": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "total": {
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
              "available",
              "total"
            ],
            "additionalProperties": false
          },
          "check": {
            "type": "object",
            "properties": {
              "cpuIds": {
                "oneOf": [
                  {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "platform": {
                "type": "string"
              },
              "battery": {
                "oneOf": [
                  {
                    "type": "boolean"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "virtualized": {
                "oneOf": [
                  {
                    "type": "boolean"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "taskset": {
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
              "cpuIds",
              "platform",
              "battery",
              "virtualized",
              "taskset"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "cpuCount",
          "load",
          "memory",
          "pressure",
          "disk"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "files.read",
        "files.stat",
        "fs.readdir",
        "os.cpuCount",
        "os.load",
        "os.memory",
        "os.statfs",
        "os.detectVirt"
      ]
    },
    {
      "operation": "machineCheckPorts",
      "input_schema": {
        "type": "object",
        "properties": {
          "platform": {
            "type": "string"
          },
          "env": {
            "type": "object",
            "properties": {
              "PATH": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": [
          "platform"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "cores": {
            "type": "array",
            "items": {
              "type": "integer"
            }
          },
          "platform": {
            "type": "string"
          },
          "battery": {
            "type": "boolean"
          },
          "virtualized": {
            "type": "boolean"
          },
          "taskset": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "memory": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          },
          "load": {
            "oneOf": [
              {
                "type": "number"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "cores",
          "platform",
          "battery",
          "virtualized",
          "taskset",
          "memory",
          "load"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "files.read",
        "files.stat",
        "fs.readdir",
        "os.cpuCount",
        "os.load",
        "os.memory",
        "os.detectVirt"
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
              "content"
            ],
            "additionalProperties": false
          }
        },
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
                "type": "integer"
              }
            },
            "required": [
              "exists",
              "is_symlink",
              "size"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "fs",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readdir",
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
              "entries": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "entries"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "os",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "cpuCount",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "count": {
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
              "count"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "load",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "oneOf": [
                  {
                    "type": "number"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "value"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "memory",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "available": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "total": {
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
              "available",
              "total"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "statfs",
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
              "bavail": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "blocks": {
                "oneOf": [
                  {
                    "type": "integer"
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "bsize": {
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
              "bavail",
              "blocks",
              "bsize"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "detectVirt",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "status": {
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
              "status"
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
  "conventions": []
}
```
</details>
