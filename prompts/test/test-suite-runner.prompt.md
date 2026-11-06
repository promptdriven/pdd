# Node test suite runner

This new module owns the child process used by the package's `npm test` entry. `src/test-suite-runner.mjs` exports module function `runTestSuite({cwd, testFiles, environment}, ports)`. It starts the selected Node test files through the injected `nodeTest.run` program port and returns that run's exit status and captured output unchanged.

Before launch, omit every environment entry whose name starts with `HERDR_` or equals `PDD_AGENT_SESSION`. Keep all other supplied entries and values. Set child stdio to `["ignore", "pipe", "pipe"]`: the child gets no caller input and does not inherit the caller's output streams. Do not connect to or read a Herdr or agent session. Wait for the Node test process to exit, then return its `exit_code`, `stdout` and `stderr` unchanged. Do not hide test failures or diagnostics.

The `environment` input is one row per variable. Preserve each supplied `testFiles` item and its order.

The interpreter can check only the injected launch arguments and supplied program replies. Real process creation, environment inheritance, file descriptors and termination are native effects. A passing prompt check does not prove that the OS child has no live socket or that an actual test process exits.

## Dependencies

- [Package scripts](../../package.json), required for authoring and native verification of how `npm test` selects the suite and enters this new module.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "c8d88e91576c6a481a30c698cce7b754c30b21e3742216af5fb0338f56fd438d",
  "entries": [
    {
      "operation": "runTestSuite",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {"type": "string", "minLength": 1},
          "testFiles": {"type": "array", "items": {"type": "string", "minLength": 1}, "minItems": 1},
          "environment": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {"name": {"type": "string", "minLength": 1}, "value": {"type": "string"}},
              "required": ["name", "value"],
              "additionalProperties": false
            }
          }
        },
        "required": ["cwd", "testFiles", "environment"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {"exit_code": {"type": "integer"}, "stdout": {"type": "string"}, "stderr": {"type": "string"}},
        "required": ["exit_code", "stdout", "stderr"],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "nodeTest",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "run",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {"type": "string", "minLength": 1},
              "testFiles": {"type": "array", "items": {"type": "string", "minLength": 1}, "minItems": 1},
              "environment": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {"name": {"type": "string", "minLength": 1}, "value": {"type": "string"}},
                  "required": ["name", "value"],
                  "additionalProperties": false
                }
              },
              "stdio": {"type": "array", "items": {"type": "string", "enum": ["ignore", "pipe"]}, "minItems": 3, "maxItems": 3}
            },
            "required": ["cwd", "testFiles", "environment", "stdio"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {"exit_code": {"type": "integer"}, "stdout": {"type": "string"}, "stderr": {"type": "string"}},
            "required": ["exit_code", "stdout", "stderr"],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {"max_steps": 4, "max_model_calls": 12},
  "conventions": []
}
```

</details>
