# Confirm scope and observable expectations

Before drafting any Story, read the **entire** [Prompting guide](../../../docs/prompting-guide.md) into this agent conversation, including in an existing chat. Summarize the relevant method: describe what and why, preserve observable behavior and consequential edge cases, give each rule one owner, and keep expected results independent of implementation. Then apply it. A link, filename, prior chat summary or format check does not load the guide. If the file is unavailable, ask for its contents before drafting.

Read repository instructions and the affected public behavior. State the requested result, affected surface, why it is contained and how to undo it. Identify a concrete expected output or error independently of implementation when behavior changes.

Use the authorization already given. Resolve material ambiguity before expanding the edit; do not turn a contained task into broad prompt adoption or require a new Story for a trivial correction.

In a runner stage, save plan-only cases and notes under the supplied artifactDirectory in Git metadata. List them in the handoff with storage:"run" and paths relative to that directory. Keep these files out of the project worktree and PR. Actual project deliverables retain project-relative paths and must be committed by the change stage.
