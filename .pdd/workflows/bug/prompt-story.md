# Draft the corrected contract, Story and regression cases

Before drafting any Story, read the **entire** [Prompting guide](../../../docs/prompting-guide.md) into this agent conversation, including in an existing chat. Summarize the relevant method: describe what and why, preserve observable behavior and consequential edge cases, give each rule one owner, and keep expected results independent of implementation. Then apply it. A link, filename, prior chat summary or format check does not load the guide. If the file is unavailable, ask for its contents before drafting.

Identify the owning canonical prompt and the accepted expectation. Correct the prompt first only if it is wrong or incomplete; otherwise preserve it and explain why the code needs repair. Describe the observable correction, compatibility boundary and forbidden regression in the Story.

Keep the actual bug input. Author its expected output/error from the accepted requirement, not the current implementation or an unchecked model answer. Include nearby boundary and unaffected cases using the project's ordinary test format. Map them to Story criteria and name anything not covered. Keep drafts and unresolved questions visible.

When launched as a runner stage, follow its exact handoff request. Prepare an intended topic branch and commit only the agreed work before a later PR stage. Preserve existing work; never force checkout, reset, stash or overwrite unrelated changes. If a safe committed topic branch cannot be established, report that limit instead of pushing or creating a PR yourself.
