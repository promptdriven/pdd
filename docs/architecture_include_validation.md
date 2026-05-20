# Architecture vs `<include>` / `<pdd-dependency>` validation

PDD cross-checks each `architecture.json` **module dependency** against the union of
the prompt's **module-prompt `<include>` tags** (paths ending in `.prompt` that map
to another module) and its **`<pdd-dependency>` declarations**. Either kind of tag
satisfies a declared arch dependency — they are both architecture edges under the
union semantics described in `docs/prompting_guide.md`. Context and example files
(e.g. `context/foo_example.py`) are not treated as architecture module edges, so the
check matches how dependency lists are usually maintained.

Path-qualified module prompts (e.g. `commands/fix_python.prompt` vs
`server/fix_python.prompt`) are compared with their directory prefix preserved, so
same-tail prompts in different folders are not silently aliased. Bare arch deps
(`fix_python.prompt`) are first resolved against the architecture file to their
unambiguous path-qualified entry before comparison.

## Commands

- **`pdd checkup --validate-arch-includes`** — validate architecture dependencies vs
  module `<include>` and `<pdd-dependency>` edges.
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
(dependency listed in JSON but no module `<include>` or `<pdd-dependency>`, or the
reverse — prompt `<include>`s a module not in the arch dependency list). Sample
output (abridged):

```
Warning: examples/arch/architecture.json: architecture.json / <include> mismatch: 'order_api_Python.prompt' declares dependency on module 'order_models' ...
Warning: examples/prompts_linter/architecture.json: architecture.json / <include> mismatch: 'pipeline_Python.prompt' declares dependency on module 'report' ...
```

CI runs `pdd checkup --validate-arch-includes` against the repo plus a small aligned
fixture under `tests/fixtures/arch_include_validate_ok/` so the step fails if the
command or validation logic regresses.

## Discovery-layer skip (used by sync and related tooling)

`pdd.architecture_registry.find_architecture_for_project` applies the same
bundled-sample skip by default: top-level `examples/`, `example_project/`,
`example_workspace/`, and `staging/` trees are excluded so a root-level
`pdd sync` (and other discovery-driven tooling such as `metadata_sync` and
`auto_deps_architecture`) does not flatten sample modules into the project's
own `architecture.json` (issue #1060). Real nested architecture files under
other top-level names (`services/`, `apps/`, `packages/`, `libs/`, `frontend/`,
`backend/`, etc.) are still discovered.

If your monorepo intentionally uses one of the four sample names for production
modules, opt back in by passing `skip_bundled_sample_arch=False` to the
discovery helper, or run the validator with `pdd checkup --validate-arch-includes
--strict`. The skip is a no-op when the project root is itself a bundled-example
directory, so scans started inside one of those trees continue to work.
