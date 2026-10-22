# Workflows

Choose the smallest recipe that fits the change. Each recipe is reusable Markdown under `.pdd/workflows/` and links to its complete step instructions.

- [Feature](../.pdd/workflows/feature/WORKFLOW.md): define a new behavior, create a visual direction when there is a visible interface, review prompts, then implement and check code.
- [Bug](../.pdd/workflows/bug/WORKFLOW.md): reproduce a defect, express the corrected behavior in its prompt and examples, then implement and review the fix.
- [Small change](../.pdd/workflows/small-change/WORKFLOW.md): make a contained, reversible change in one PR without requiring prompt-space adoption.

For prompt changes, the person approves the current prompt and Story before the Prompt PR. When a prompt changed, that PR is reviewed and merged before code work. The Code PR receives its own review and person-controlled merge. A workflow may skip an inapplicable step, but it must say why; it must not report unavailable evidence as a pass.
