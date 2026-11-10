# Lint SVG layout agreements through Runtime file ports

I can check whether screen prompts and their linked `.ui.svg` drawings agree on controls, labels and layout regions through declared file ports.

```pdd-boundary
prompts/cli/svg-layout.prompt.md
```

## Acceptance criteria

1. A prompt whose controls, labels and layout regions match its linked `.ui.svg` drawing produces no warnings.
2. Disagreements between a prompt and its linked `.ui.svg` drawing report missing controls, unmentioned drawing labels and unspecified drawing regions in deterministic order.
3. A prompt linking to a missing `.ui.svg` drawing reports a drawing warning, and an invalid `pdd-workspace.json` fails with `workspace-config-invalid`.
