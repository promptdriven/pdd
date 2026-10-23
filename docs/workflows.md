# Workflows

Choose the smallest recipe that fits the change. Each recipe is reusable Markdown under `.pdd/workflows/` and links to its complete step instructions.

- [Feature](../.pdd/workflows/feature/WORKFLOW.md): define a new behavior, create a visual direction when there is a visible interface, review prompts, then implement and check code.
- [Bug](../.pdd/workflows/bug/WORKFLOW.md): reproduce a defect, express the corrected behavior in its prompt and examples, then implement and review the fix.
- [Small change](../.pdd/workflows/small-change/WORKFLOW.md): make a contained, reversible change in one PR without requiring prompt-space adoption.

For prompt changes, the person approves the current prompt and Story before the Prompt PR. When a prompt changed, that PR is reviewed and merged before code work. The Code PR receives its own review and person-controlled merge. A workflow may skip an inapplicable step, but it must say why; it must not report unavailable evidence as a pass.

The action after a linked step is part of the workflow's behavior. For example, `approval: story` pauses for the person's decision; `publish-prompt-pr` and `publish-code-pr` publish their respective PRs; `wait-for-merge: pr1` and `wait-for-merge: pr2` hold later work until those PRs merge. A small change uses `pr Small change` for its one PR and `wait merge` for the person's merge. Steps without an action suffix are guided agent stages.
