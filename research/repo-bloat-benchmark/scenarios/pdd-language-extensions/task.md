# Bug report: sync expects `file.yml` but generation writes `file.yaml`

`bundled_extension` is the single source of truth mapping a language name to
its canonical file extension, parsed from the package-bundled
`data/language_format.csv`. Both the sync side (paths sync *expects*) and
the generation side (paths generation *writes*) resolve through it.

The CSV intentionally lists some languages more than once (YAML appears with
`.yml` and then `.yaml`). The resolver must resolve a duplicated language
**deterministically to the extension of its first row** — that is the
recorded canonical choice. It currently resolves to the **last** row, so
`bundled_extension("YAML")` returns `"yaml"` while the rest of the toolchain
treats `"yml"` as canonical: sync looks for `module.yml`, generation writes
`module.yaml`, and every YAML prompt module appears permanently out of sync.

Expected behavior: `bundled_extension("YAML") == "yml"`, and in general a
language listed multiple times resolves to its first row. Lookups for
languages listed once, case-insensitivity, dot-stripping, and the
known-but-extensionless (`""`) / unknown (`None`) distinction must not
change.

## Constraints

- Fix the defect in the library code under `src/pdd/`.
- Do not modify anything under `tests/` or the bundled CSV.
- The visible suite (`pytest tests/visible -q`) must keep passing.
