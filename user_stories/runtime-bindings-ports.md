# Inspect module binding coverage through Runtime file and Git ports

I can validate `pdd-bindings.json` and compute selected module binding coverage through declared file and Git ports.

```pdd-boundary
prompts/cli/runtime-bindings.prompt.md
```

## Acceptance criteria

1. Inspecting a repository without `pdd-bindings.json` returns `available: false` with null counts and an empty module list.
2. Inspecting a valid `pdd-bindings.json` reports bound and unbound modules intersecting selected Stories in declaration order.
3. A malformed `pdd-bindings.json` declaration fails with `PreflightError`.
