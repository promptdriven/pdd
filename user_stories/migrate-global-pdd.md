# Migrate a global PDD installation

As a developer with the unscoped global `pdd` installation, I want upgrade to tell me how to switch packages without overwriting my executable, so I can keep using PDD.

## Acceptance criteria

1. When pdd upgrade runs from the unscoped global package, it exits with code 1, explains the npm executable collision, and prints the uninstall and install commands for that npm prefix without running them.

## Verification boundary

```pdd-boundary
prompts/cli/autopilot-update.prompt.md
```
