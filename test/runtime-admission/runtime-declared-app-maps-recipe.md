# Declared app maps verification recipe

Story: `user_stories/runtime-declared-app-maps.md`.

Use Node 22.16 or newer and Git. Run from the PDD repository root:

```sh
node --test test/runtime-declared-app-maps.test.mjs
```

The test invokes the public `scenarioShapeRefusal` and `captureSource` APIs and
starts the repository's real `bin/pdd.mjs test --files` process. It creates a new
synthetic Git repository for each case. It requires no credentials, provider,
server or model calls. Each fixture is removed after its case finishes.

The command loads this checkout's source, rather than an installed PDD package.
Keep the source revision and any working-tree diff with the retained TAP output.
Compilation and service readiness are not applicable to these Node source tests.

## Required cases

- AC1: locally accept a map declaration while the authored scenario has only the shell step.
- AC2: capture the exact map closure, including the screen prompt, its image,
  transitive prompt/data dependencies, action prompt and stylesheet. Exclude the
  unrelated tester and map. Exercise mockup source, timers, after handlers, host
  helpers and owners, and the real CLI preview too. Never scan arbitrary input data.
- AC3: refuse required missing map, screen, action and stylesheet paths;
  reject traversal and a map symlink that resolves outside the repository. Preserve
  authored workspace restrictions and Story interface projection.
- AC4: preserve unknown-key rejection and refuse malformed selected map JSON
  and malformed map lists, unsafe paths and duplicate declarations.
- AC5: preserve absent/empty selection and isolate map files in per-Story footprints.
- Control: the existing explicit caller `appMap` option captures the same closure.

Exact expected paths and results come from the Story and the synthetic fixture.
A failed assertion is a failed case. Keep setup failures separate from behavior
failures. Do not count skipped or unexecuted cases as passed.

## Scope and further checks

These cases check native behavior. They do not establish a prompt-interpreter
verdict, hosted admission, simulation-operation validation, lint/check agreement,
every workspace or Story-boundary edge case. Those
checks remain separate requirements of the Story. An independent verifier must
repeat the applicable checks from a fresh candidate checkout and retain its own
output. Run `npm test` before publishing reviewed source.
