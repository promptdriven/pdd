# Explain which pdd PATH selects through Runtime ports

I can inspect `which -a pdd` candidates, identify symlinks to the running pdd, probe a shadowing candidate's `--version`, and emit setup, version or workflow diagnostics through declared ports.

```pdd-boundary
prompts/cli/path-diagnostic.prompt.md
```

## Acceptance criteria

1. In `setup` mode when another `pdd` shadows a symlink to this `pdd` on `PATH`, `pathDiagnostic` probes only the selected candidate once, lists the candidates in order, explains environment-activation PATH reordering, and outputs both the absolute Node-plus-pdd command and the `export PATH` + `hash -r` fix.
2. In `workflow` mode when `PATH` selects a different `pdd`, `pathDiagnostic` returns a single one-line shadowing warning with `"$PDD_BIN"`, and when `PDD_PATH_DIAGNOSTIC_PROBE` is `"1"`, returns `lines: []` without calling `host.whichPdd` or `host.probeVersion`.
3. Passing an unsupported `mode` fails with `invalid_path_diagnostic_mode`.
