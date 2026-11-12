As a person who updates global npm tools, I want pdd to use the owned package name and tell me how to update safely, so that npm cannot replace it with the unrelated pdd package.

## Acceptance criteria

1. `pdd setup` and `pdd autopilot doctor` warn about the old npm name `pdd` and show `npm uninstall -g pdd && npm install -g github:promptdriven/pdd`, without changing installed packages.
2. With the scoped GitHub distribution and no old package, setup and doctor warn against `npm update -g` for pdd and show `npm install -g github:promptdriven/pdd`.
3. An installed scoped package also detects the old global package beside it and shows the migration command; a source checkout does not mistake a project-local pdd folder for a global install.
4. Missing or malformed package metadata does not stop setup or doctor or produce a false legacy migration warning.

The npm package is `@promptdriven/pdd`, the command stays `pdd`, and publishing to npm is outside this issue. Install and update from GitHub until publication. README shows the migration command before installation for anyone with the old name.

```pdd-boundary
prompts/cli/path-diagnostic.prompt.md
```

The Runtime cases check the shared package advice. Native tests check setup and doctor consume it, package identity, and isolated npm installation/update behavior. Real registry availability is a separate experiment.
