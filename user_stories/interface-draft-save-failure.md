# Keep prompts unchanged when draft provenance cannot be saved

As a prompt author, I want a failed interface draft save to leave my prompt unchanged, so that a failed command cannot reopen approval or add unsaved declarations.

## Acceptance criteria

1. When `pdd interface draft prompts/percent.prompt.md --json` cannot create its local provenance file, the command exits 2 and the prompt remains byte for byte unchanged, with no Runtime interface added and no provenance record created.
2. When `pdd interface draft prompts/percent.prompt.md --extend --contract contracts/add.json --json` cannot update its local provenance file, the command exits 2 and the approved prompt remains byte for byte unchanged, including its approval status, prose hash and declarations. Existing provenance remains byte for byte unchanged.
3. When one selected prompt fails its own validation, an independent valid prompt still drafts successfully and retains its saved provenance. The refused prompt remains unchanged and the command reports both outcomes with a nonzero exit code.

## Rules to check

A failed provenance save must leave each affected prompt exactly as it was before the command. The forbidden result is a failed save that changes prompt bytes, adds an interface or changes approval status. This rule does not turn an independent per-prompt validation refusal into an all-or-nothing batch: successful independent rows and their provenance must survive that refusal.

The existing [owning prompt](../prompts/cli/interface-draft.prompt.md) already requires these behaviors and stays unchanged. Error diagnostic wording, Runtime response diagnostics and approval policy are outside this repair.

[Native CLI cases](../test/interface-draft-save-failure.test.mjs) use isolated Git projects and real filesystem permissions. The independent validation case runs normally.

The owning prompt has no Runtime interface for executing this behavior. This Story has no Runtime scenario file. A PDD interpreter check is therefore not available through the current contract; native test results are separate evidence and do not establish a prompt-interpreter pass.
