# Explain which pdd PATH selects

Own `src/path-diagnostic.mjs`, exporting `pathDiagnostic({packageRoot, cwd, env, mode})`, which returns diagnostic lines without writing files or changing installations. Help a person running this pdd by an absolute path understand why a plain `pdd` can run a different program. Preserve the CLI's version-only stdout and ordinary command results.

Read this package's version and executable identity locally. Discover executable `pdd` paths in order with `which -a pdd`; if `which` is unavailable, enumerate executable files in PATH with the same relative/empty-directory semantics. Deduplicate repeated paths; recognize symlinks to this pdd executable as the same program. Do not mistake a missing, nonexecutable or broken file for a candidate. A missing package/executable supplies no diagnostic.

When setup requests the full report, identify this running pdd executable and version, list the PATH candidates in order, and identify the first candidate and its version. If it is this pdd, use the known version. Otherwise probe only that selected executable with `--version`, never with setup or an operational command. Bound the probe to two seconds and 64 KiB; a nonzero exit, timeout, inaccessible or empty version reports version unavailable without suppressing the path or disrupting the command. Use a private environment recursion guard so probing another copy of this pdd does not launch another diagnostic. Sanitize child text to one readable line; never echo child stderr, environment values or raw errors.

For a conflict (the selected executable differs, or another distinct pdd is present), explain that a later environment activation, such as conda, can reorder PATH and shadow this pdd again. Give the verified absolute Node-plus-pdd command. If a verified executable named `pdd` on PATH points to this pdd, also give its bin-directory PATH correction, applied **after** environment activation, plus `hash -r`. Never suggest a PATH directory that lacks this pdd's command named `pdd`. Do not remove or replace another install, change PATH, ask a removal question, or run a package manager.

`mode: 'workflow'` returns only a one-line shadowing warning for workflow startup, including the selected path/version and the absolute command for this pdd; no warning when PATH selects this pdd. `mode: 'version'` emits the full report only for a conflict. `mode: 'setup'` emits the report even without a conflict. Diagnostics remain local: no runtime, authentication or agent calls.

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring. The [CLI](pdd-cli.prompt.md) owns dispatch and output streams.
- Runtime: Node filesystem, child-process and path primitives provide local discovery and bounded version probes. Package metadata and `bin/pdd.mjs` identify the running pdd.
