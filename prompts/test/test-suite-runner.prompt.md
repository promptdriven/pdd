# Node test-suite launcher

`src/test-suite-runner.mjs` exports module function `runTestSuite({cwd, testFiles, environment}, ports)`. The npm test entry runs this module and passes its numeric child exit code to npm.

## Entry and file selection

The package script must be `"test": "node src/test-suite-runner.mjs"`. The entry calls `runTestSuite` with the current working directory, positional test-file arguments and environment. With no test-file arguments, start the current Node executable with `["--test", "test/*.test.mjs"]`, preserving the existing top-level suite selection. When invoked as `npm test -- <file...>`, start it with `["--test", ...testFiles]`; only those supplied paths run. Do not append a focused selection to the full suite or invoke a shell.

Call the injected `nodeTest.run` once with the selected Node arguments. Remove each environment entry whose name starts with `HERDR_` or equals `PDD_AGENT_SESSION`; preserve every other supplied name and value. Set child stdio to `["ignore", "pipe", "pipe"]`. The child receives no caller stdin. Forward each stdout and stderr chunk to the matching caller stream as soon as it arrives, preserving each stream's bytes and order. Do not accumulate and replay output after exit, add a timeout, or print a replacement diagnostic. Wait for the child to close and return its numeric exit code unchanged, including nonzero codes.

Do not inspect or connect to a Herdr socket or agent session. This contract filters the named environment entries and ignores caller stdin. It intentionally preserves caller-visible stdout and stderr through live per-chunk forwarding. It does not promise to remove every inherited descriptor or prove socket isolation.

The scenario can check the selected arguments, filtered environment, stdio choice and supplied exit code. It cannot model stream events or prove live forwarding, OS descriptor behavior or that a real child terminates. Those effects need native checks.

## Dependencies

- [Package scripts](../../package.json), required to keep the `npm test` entry, its default `test/*.test.mjs` selection and focused-file arguments aligned.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "caefd075eebf30d20022d45859967a51b1e3236eec884b793f3c2b6023e92f1c",
  "entries": [
    {
      "operation": "runTestSuite",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {"type": "string", "minLength": 1},
          "testFiles": {"type": "array", "items": {"type": "string", "minLength": 1}},
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
        "properties": {"exit_code": {"type": "integer"}},
        "required": ["exit_code"],
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
              "args": {"type": "array", "items": {"type": "string"}},
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
            "required": ["cwd", "args", "environment", "stdio"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {"exit_code": {"type": "integer"}},
            "required": ["exit_code"],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {"max_steps": 12, "max_model_calls": 12},
  "conventions": []
}
```

</details>
