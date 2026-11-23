# Explain which pdd PATH selects

Own `src/path-diagnostic.mjs`, exporting `pathDiagnostic({packageRoot, cwd, env, mode})`, which returns diagnostic lines without writing files or changing installations.

## Domain decisions

- Read this package's version and executable identity locally. Discover executable `pdd` paths in order with `which -a pdd`; if `which` is unavailable, enumerate executable files in `PATH` with the same relative/empty-directory semantics. Deduplicate repeated paths; recognize symlinks to this `pdd` executable as the same program.
- Probe only a shadowed first candidate with `--version` (bounded to 2 seconds and 64 KiB, with `PDD_PATH_PROBE=1` recursion guard). Sanitize child text to one readable line.
- **Quiet when clean:** for `mode: 'version'` and `mode: 'setup'`, emit `[]` when `PATH` cleanly selects this `pdd` with no conflict, no extra distinct `pdd`, and no unscoped npm `"pdd"` package. For `mode: 'workflow'`, emit a one-line shadowing warning only when shadowed (including `"$PDD_BIN"`).
- **Conflict remediation:** when an unrelated unscoped npm `"pdd"` package or legacy unscoped `"pdd"` CLI package is detected next to a `PATH` directory, recommend `npm uninstall -g pdd && npm install -g @promptdriven/pdd` (never `--force` and never the old `github:promptdriven/pdd` URL).
- Never remove or replace another install, change `PATH`, ask a question, or run a package manager.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Navigation only: [CLI](pdd-cli.prompt.md) owns dispatch and output streams.
