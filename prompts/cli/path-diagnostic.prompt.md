# Explain which pdd PATH selects

Own `src/path-diagnostic.mjs`, exporting `pathDiagnostic({packageRoot, cwd, env, mode})`, which returns diagnostic lines without writing files or changing installations. Help a person running this pdd by an absolute path understand why a plain `pdd` can run a different program. Preserve the CLI's version-only stdout and ordinary command results.

Read this package's version and executable identity locally. Discover executable `pdd` paths in order with `which -a pdd`; if `which` is unavailable, enumerate executable files in PATH with the same relative/empty-directory semantics. Deduplicate repeated paths; recognize symlinks to this pdd executable as the same program. Do not mistake a missing, nonexecutable or broken file for a candidate. A missing package/executable supplies no diagnostic.

When setup requests the full report, identify this running pdd executable and version, list the PATH candidates in order, and identify the first candidate and its version. If it is this pdd, use the known version. Otherwise probe only that selected executable with `--version`, never with setup or an operational command. Bound the probe to two seconds and 64 KiB; a nonzero exit, timeout, inaccessible or empty version reports version unavailable without suppressing the path or disrupting the command. Use a private environment recursion guard so probing another copy of this pdd does not launch another diagnostic. Sanitize child text to one readable line; never echo child stderr, environment values or raw errors.

For a conflict (the selected executable differs, or another distinct pdd is present), explain that a later environment activation, such as conda, can reorder PATH and shadow this pdd again. Give the verified absolute Node-plus-pdd command. If a verified executable named `pdd` on PATH points to this pdd, also give its bin-directory PATH correction, applied **after** environment activation, plus `hash -r`. Never suggest a PATH directory that lacks this pdd's command named `pdd`. Do not remove or replace another install, change PATH, ask a removal question, or run a package manager.

`mode: 'workflow'` returns only a one-line shadowing warning for workflow startup, including the selected path/version and a short `"$PDD_BIN"` hint for workflow chats; no warning when PATH selects this pdd. `mode: 'version'` emits the full report only for a conflict. `mode: 'setup'` emits the report even without a conflict. Diagnostics remain local: no runtime, authentication or agent calls.

## Safe package updates

Also own `packageInstallDiagnostic({packageRoot}, ports = {})`, returning exactly
`{kind, detail, fix}`. `kind` is `legacy`, `github` or `none`; `detail` and `fix`
are strings, empty for `none`. Read JSON package metadata through
`ports.files.readFileSync(path, 'utf8')` (Node filesystem by default). Missing,
unreadable or malformed metadata is absent evidence, never a command failure.
No package manager is invoked and no installation is changed.

The npm package name is `@promptdriven/pdd`; the executable remains `pdd`.
Publication is outside this change. Until publication, install and update with
`npm install -g github:promptdriven/pdd`, never `npm update -g` for pdd.

When this package's metadata has the old name `pdd`, return `legacy`. When this
package has name `@promptdriven/pdd` and its root is
`<node_modules>/@promptdriven/pdd`, also inspect
`<node_modules>/pdd/package.json`: name `pdd` there takes precedence and returns
`legacy`, even if npm has replaced it with the unrelated registry package.
The legacy detail warns against `npm update -g` and explains that the old npm name can be replaced by an unrelated
package and that both names can compete for the `pdd` command. Its fix is exactly
`npm uninstall -g pdd && npm install -g github:promptdriven/pdd`.
Otherwise the scoped name returns `github`, with a detail that pdd is distributed
from GitHub, the scoped package is not yet published, and `npm update -g` must
not be used for pdd; its fix is the install/update command above. This guidance
also applies to source checkouts: npm does not reliably preserve GitHub origin
metadata. Any other or unreadable own metadata returns `none` without inspecting
unrelated directories. Never infer a global legacy package from a project-local
`pdd` directory outside the installed scoped layout.

In `mode: 'setup'`, append the package diagnostic detail and `Update with: FIX`
when kind is not `none`, even if PATH evidence is unavailable. Other modes keep
their existing output. The doctor's caller consumes this same package policy.

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring. The [CLI](pdd-cli.prompt.md) owns dispatch and output streams.
- Runtime: Node filesystem, child-process and path primitives provide local discovery and bounded version probes. Package metadata and `bin/pdd.mjs` identify the running pdd.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "partial",
  "status": "draft",
  "prose_sha256": "6b85dffed08a1ba532ccdc1686cec4cab337ae0ce4fe1e278c81b0cce73093f0",
  "entries": [
    {
      "operation": "packageInstallDiagnostic",
      "input_schema": {
        "type": "object",
        "properties": {
          "packageRoot": {
            "type": "string"
          }
        },
        "required": [
          "packageRoot"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "kind": {
            "type": "string",
            "enum": [
              "legacy",
              "github",
              "none"
            ]
          },
          "detail": {
            "type": "string"
          },
          "fix": {
            "type": "string"
          }
        },
        "required": [
          "kind",
          "detail",
          "fix"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "files",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readFileSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "found": {
                "type": "boolean"
              },
              "text": {
                "type": "string"
              }
            },
            "required": [
              "found",
              "text"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 3,
    "max_model_calls": 3
  },
  "conventions": []
}
```

</details>
