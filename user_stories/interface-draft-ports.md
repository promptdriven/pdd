# Draft, inspect and automatically approve Runtime interfaces through Runtime ports

I can inventory missing or invalid Runtime interfaces, compute prose contract coverage, draft interfaces from explicit contracts, and run automatic approval through declared Git, file, compute, execution, approval and output ports.

```pdd-boundary
prompts/cli/interface-draft.prompt.md
```

## Acceptance criteria

1. `missingInterfaces`, `interfaceFindings`, `cliInterfaceFindings` and `runtimeCoverage` report missing declarations, schema findings and checkable counts across workspace prompts.
2. `contractCoverage` and `coverageView` map prose sentences to interface pointers and format coverage lines.
3. `runInterfaceDraft` installs a supplied contract into an undeclared prompt and `runAutomaticApproval` approves a clean draft after passing native tests and prompt checks.
4. Unavailable roots, missing prompts, invalid coverage reports, empty draft working directories and refused automatic approvals fail with their declared error codes.
