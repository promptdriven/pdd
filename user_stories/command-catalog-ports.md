# Inspect command catalog exports through Runtime entries

I can inspect the public command names, bundled workflow names, help text templates, route ids, route specifications and manifest help forms, and receive clear errors for unknown keys or route ids.

```pdd-boundary
prompts/cli/command-catalog.prompt.md
```

## Acceptance criteria

1. `NAMES`, `BUNDLED_WORKFLOW_NAMES` and `PUBLIC_HELP_TEXT` return the canonical command words, bundled workflow list and help text templates.
2. `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_ROUTES` and `PUBLIC_COMMAND_MANIFEST` return route membership, route specifications and help form descriptions for cataloged commands.
3. Unknown keys, workflow names, help sections, route ids and help forms fail with `unknown-command-name`, `unknown-workflow-name`, `unknown-help-section`, `unknown-route-id` and `unknown-help-form`.
