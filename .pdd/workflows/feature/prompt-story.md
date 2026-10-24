# Draft the prompt, Story and independent cases

Before drafting any Story, read the **entire** [Prompting guide](../../../docs/prompting-guide.md) into this agent conversation, including in an existing chat. Summarize the relevant method: describe what and why, preserve observable behavior and consequential edge cases, give each rule one owner, and keep expected results independent of implementation. Then apply it. A link, filename, prior chat summary or format check does not load the guide. If the file is unavailable, ask for its contents before drafting.

Write or update the owning canonical prompt before implementation. Describe purpose, inputs, public invocation, results/errors, boundaries and forbidden effects. Preserve the agreed compatibility promise. Declare required context in one Dependencies section; actually read it before using it.

Draft a Story with observable acceptance criteria and exclusions. Author concrete inputs and expected outputs or errors from those requirements **before using implementation output as evidence**. Include important normal, boundary and failure cases and map them to criteria. Use the project's existing case format or a small clearly documented one; a JSON file is not automatically executable by PDD. Mark unresolved decisions and drafts honestly.

Keep policy in its owning prompt; the Story and cases should make that policy observable rather than invent a second rule set. For a UI, link the accepted view and explain interaction/accessibility in the prompt.

When launched as a runner stage, follow its exact handoff request. Prepare an intended topic branch and commit only the agreed work before a later PR stage. Preserve existing work; never force checkout, reset, stash or overwrite unrelated changes. If a safe committed topic branch cannot be established, report that limit instead of pushing or creating a PR yourself.
