As a workflow operator, I want approved workflow changes to refresh PR descriptions with Ubuntu's GitHub CLI, so that I can read current prompts, evidence and next steps.

## Acceptance criteria

1. Workflow PR descriptions update through the pull request REST endpoint even when gh pr edit would fail with the Projects classic deprecation error; the complete multiline description is retained.
2. A rejected description update shows gh's diagnostic on one safe line with a retry command, including when gh returns an exit code or throws an error; terminal controls and credentials are not exposed.
3. If the code choice is recorded but its PR 1 update fails, the advertised retry repairs the missing approval after gh is restored, without another approval or run advance. A later status refresh keeps that approval visible above Details. A changed remote description or head prevents overwriting newer work.
4. Existing draft, head, progress, publication-pending and custody checks still apply: a failed pending description update prevents a new source push, and a failed final update does not claim current evidence.

## Verification

The [workflow runner](../prompts/cli/workflow-runner.prompt.md)'s existing partial Runtime interface does not expose publication or approval operations and its program port cannot carry description stdin or stderr. Native tests exercise the public runner operations with isolated Git repositories and a controlled gh boundary. No new Runtime interface is introduced for this repair.

Run `node --test test/workflow-pr-description.test.mjs` for the native regression. The publication suite also covers PR 1 approval failures and retrying a legacy PR 2 link without changing its evidence section.
