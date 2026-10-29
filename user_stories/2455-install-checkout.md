# Install and select a checkout build

As a tester working from a source checkout, I can run the development installer, have it create the managed installation record and required runtime/tool layout, select that checkout build as active, and see the derived development version.

## Acceptance criteria

1. Running the approved development-install command for a checkout succeeds, creates the managed version record with its required runtime and Node-tool entries, and selects that development version as active.
2. The command reports the checkout package version with the approved development suffix (for example, `0.1.9-dev`) and ends successfully.
3. An existing active installation and its prior selection remain recoverable for the matching uninstall.

## Rules to check

- The development version is derived from the checkout package metadata and is distinguishable from a signed release.
- A failed install must not leave partial managed state or silently replace an unrelated active installation.
