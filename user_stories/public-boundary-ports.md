# Local PDD command boundary ports

I can route local PDD commands without calling the PDD interpreter, allow only `test`, `lint`, `simulate`, and `mcp` to call the PDD interpreter, refuse removed or excluded commands before any effect, and enforce person-facing versus machine-read terminology.

```pdd-boundary
prompts/cli/public-boundary.prompt.md
```

## Acceptance criteria

1. `dispatchBoundaryCommand` routes local commands (`workflow view`, `metrics`, `setup`, `--help`) through `local.dispatch` with `usesInterpreter: false` and zero `interpreter.call` invocations, and routes `test`, `lint`, `simulate`, and `mcp` through `interpreter.call` with `usesInterpreter: true`.
2. `dispatchBoundaryCommand` refuses excluded or removed commands (`session`, `workflow feature`, `check`, `try`) with `{exitCode: 2, route: "refused", usesInterpreter: false}` and a diagnostic on `output.stderr` before calling `local.dispatch` or `interpreter.call`, and raises `empty-command-argv` when `argv` is empty.
3. `validateBoundaryText` accepts `"the PDD interpreter"`, `pdd test`, `pdd lint`, `pdd simulate`, and `pdd workflow run` on `"person"` lines as well as `"runtime"` and `"check"`/`"try"` tokens on `"machine"` or `"server"` lines, and raises `forbidden-boundary-word` when a `"person"` line says `"PDD runtime"`, `"the runtime"`, `"pdd check"`, or `"pdd try"`.
