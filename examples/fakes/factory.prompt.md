# factory

`factory.mjs` exports module function createGreeter(prefix), returning an object with method greet(name). Each greeter captures its own prefix; greet returns `{text: prefix + name}` without changing it. Runtime createGreeter is a factory: read prefix from logical arguments, store `{prefix}` via instances.store using the executor-issued instance_handle, and return that exact handle. Runtime greet receives handle and name, loads captured config once via instances.load and returns the greeting. Handles are opaque; never invent them. The collection represents closure state, not a new public argument to the native method.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "831d85b3374238f9a87c574e6c2933be329a451ec2c2236ba8e21f8dda0f8144",
  "entries": [
    {
      "operation": "createGreeter",
      "input_schema": {
        "type": "object",
        "properties": {
          "prefix": {
            "type": "string"
          }
        },
        "required": [
          "prefix"
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
      "errors": [],
      "instance": {
        "kind": "factory",
        "type": "Greeter",
        "path": "/handle"
      },
      "resource_operations": [
        "instances.store"
      ]
    },
    {
      "operation": "greet",
      "input_schema": {
        "type": "object",
        "properties": {
          "handle": {
            "type": "string"
          },
          "name": {
            "type": "string"
          }
        },
        "required": [
          "handle",
          "name"
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
      "errors": [],
      "instance": {
        "kind": "method",
        "type": "Greeter",
        "path": "/handle"
      },
      "resource_operations": [
        "instances.load"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "instances",
      "kind": "collection",
      "access": "write",
      "operations": [
        {
          "name": "store",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "handle": {
                "type": "string"
              },
              "config": {
                "type": "object",
                "properties": {
                  "prefix": {
                    "type": "string"
                  }
                },
                "required": [
                  "prefix"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "handle",
              "config"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "config": {
                "type": "object",
                "properties": {
                  "prefix": {
                    "type": "string"
                  }
                },
                "required": [
                  "prefix"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "load",
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
              "config": {
                "type": "object",
                "properties": {
                  "prefix": {
                    "type": "string"
                  }
                },
                "required": [
                  "prefix"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "config"
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
  "conventions": [{"path": "/entries/0/result_schema/properties/handle", "convention": "handle"}, {"path": "/entries/1/input_schema/properties/handle", "convention": "handle"}],
  "schema_version": "prompt-runtime.interface.v2",
  "instance_types": [
    {
      "name": "Greeter",
      "resource": "instances"
    }
  ]
}
```
</details>
