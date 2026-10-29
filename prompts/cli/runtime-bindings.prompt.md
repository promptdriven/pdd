# Local module binding inventory

Own `src/runtime-bindings.mjs`, exporting `bindingCoverage({root, found, selected})`.
Implement the local inventory contract in [runtime bindings](../../docs/runtime-bindings.md): limit the file to 64 KiB and 1000 module declarations; validate the complete inventory before any network or sign-in, including safe Git-visible regular paths without symlink ancestors, exact keys, known Stories and unique declarations. Throw `PreflightError` exit 4 for malformed declarations with the module/path and reason. Return `{available,bound,total,modules}` for modules intersecting selected Stories; absent inventory returns false/null/null/empty. A selected prompt declaration must reach an executable Runtime interface through the selected tests' entries and declared calls. Validate declaration shape and paths even for unselected modules; only selected declarations require selected reachability. Preserve declaration order.

## Dependencies

- [Inventory contract](../../docs/runtime-bindings.md), required for generation and verification.
- [Preflight](runtime-preflight.prompt.md), required for the existing `PreflightError` and `readPrompt` exports and discovery record shapes.
