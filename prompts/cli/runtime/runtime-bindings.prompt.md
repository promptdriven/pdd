# Local module binding inventory

Own `src/runtime/runtime-bindings.mjs`, exporting `bindingCoverage({root, found, selected, includeRuntime=false})`.
Implement the local inventory contract in [runtime bindings](../../../docs/runtime-bindings.md): limit the file to 64 KiB and 1000 module declarations; validate the complete inventory before any network or sign-in, including safe Git-visible regular paths without symlink ancestors, exact keys, known Stories and unique declarations. Throw `PreflightError` exit 4 for malformed declarations with the module/path and reason. Return `{available,bound,total,modules}` for modules intersecting selected Stories; absent inventory returns false/null/null/empty. A selected prompt declaration must reach an executable Runtime interface through the selected tests' entries and declared calls. Validate declaration shape and paths even for unselected modules; only selected declarations require selected reachability. Preserve declaration order.

## Workspace inventory use

Use the [workspace authority](runtime-workspace.prompt.md) before reading any declared source, prompt or Story. The root binding inventory is local control metadata, never permission for excluded source or automatic context. Preserve complete inventory shape/identity validation and strict executable no-link rules; optional excluded source is not opened just to compute coverage. Mark affected selected coverage unavailable with its cause instead of manufacturing a bound count or globally refusing unrelated selected work. A selected required prompt crossing remains a local preflight refusal.


## Dependencies

- [Runtime prompt inventory](interface-draft.prompt.md#inventory-results): required generation and verification context for the additive repository `runtime` coverage shape and counting rules.

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.

- [Inventory contract](../../../docs/runtime-bindings.md), required for generation and verification.
- [Preflight](runtime-preflight.prompt.md), required for the existing `PreflightError` and `readPrompt` exports and discovery record shapes.

## Runtime prompt coverage

Preserve the default `{available,bound,total,modules}` result for inventory consumers. Only `includeRuntime: true` composes the interface drafting owner's repository coverage as additive `runtime`, including absent inventory. The CLI requests this option; inventory-only consumers do not scan unrelated prompts. Preserve module binding semantics.
