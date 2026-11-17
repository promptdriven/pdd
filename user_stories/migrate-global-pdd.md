# Migrate a global PDD installation

As a developer with the unscoped global `pdd` installation, I want upgrade to tell me how to switch packages without overwriting my executable, so I can keep using PDD.

## Acceptance criteria

1. When `pdd upgrade` runs from the unscoped global package, it exits with code 1 and explains the executable collision, giving the uninstall and install commands for the same npm prefix without running them.
