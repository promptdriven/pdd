# Architecture vs `<include>` validation

PDD cross-checks each `architecture.json` **module dependency** against **module prompt**
`<include>` tags (paths ending in `.prompt` that map to another module). Context and
example files (e.g. `context/foo_example.py`) are not treated as architecture module
edges, so the check matches how dependency lists are usually maintained.

## Commands

- **`pdd checkup --validate-arch-includes`** — recommended entry point (same behavior as
  `pdd validate-arch-includes`).
- **`pdd checkup --validate-arch-includes --strict`** — also validates bundled sample
  trees (`examples/`, `example_project/`, …). The PDD repo’s sample projects currently
  report many mismatches (declarative deps vs minimal teaching prompts); use this for
  maintainer audits or while cleaning those fixtures.
- **`pdd sync --dry-run`** — still prints the same warnings for the current project
  (normal sync no longer runs this scan).

## Example: strict run on this repository

From the repo root:

```bash
pdd checkup --validate-arch-includes --strict
```

You should see warnings listing each `architecture.json` path and the kind of drift
(dependency listed in JSON but no module `<include>`, or the reverse). Sample output
(abridged):

```
Warning: examples/arch/architecture.json: architecture.json / <include> mismatch: 'order_api_Python.prompt' declares dependency on module 'order_models' ...
Warning: examples/prompts_linter/architecture.json: architecture.json / <include> mismatch: 'pipeline_Python.prompt' declares dependency on module 'report' ...
```

CI runs `pdd checkup --validate-arch-includes` against the repo plus a small aligned
fixture under `tests/fixtures/arch_include_validate_ok/` so the step fails if the
command or validation logic regresses.
