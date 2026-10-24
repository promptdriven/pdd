# Small-change recipe

Use this for a contained, reversible change with a clear effect and limited impact.

Use these instructions manually in your existing coding-agent conversation, or select this bundled workflow with `pdd workflow run NAME ISSUE` (replace NAME with this workflow's directory name). The local runner starts a fresh background native agent conversation for each agent step, supplies only the current stage request plus prior artifact pointers, pauses for recorded human choices, and uses normal Git/GitHub tools for actual PR stages. It does not execute prompts through a private service or merge PRs. In manual use, continue in your chosen conversation and publish only when asked.

When launched by the runner, obey the supplied current-stage request and handoff protocol. The overview does not authorize an agent to perform later steps. The runner owns push/PR creation; an agent must not duplicate those effects. The runner assigns a separate issue worktree and sends this saved current-stage request to a fresh owned background native conversation. Complete the real stage files and closed handoff, report the result, then stop working; no manual native exit is required. The foreground PDD controller waits for observed native activity and settlement, then independently validates the exact handoff, revisions, file hashes and required tests. Idle, a model turn or a handoff write alone never certifies success. Do not terminate the parent or launch a future stage. After the controller exits, advancement requires explicit resume of the saved run. Active attachment uses `pdd workflow attach RUN_ID`; completed stage history is archived rather than retained as a live pane.

## Before you begin

Before drafting any Story, read the **entire** [Prompting guide](../../../docs/prompting-guide.md) into this agent conversation, including in an existing chat. Summarize the relevant method: describe what and why, preserve observable behavior and consequential edge cases, give each rule one owner, and keep expected results independent of implementation. Then apply it. A link, filename, prior chat summary or format check does not load the guide. If the file is unavailable, ask for its contents before drafting.

1. [Confirm scope and observable expectations](scope.md)
2. [Make the change](change.md)
3. [Run focused native checks](verify.md)
4. [Prepare one reviewable change](open-pr.md)
5. [Leave merge to the normal process](wait-merge.md)

A new Story or broad prompt adoption is unnecessary for a small edit. If a Story is useful, load the guide before drafting it. Update an existing owning prompt first when its behavior changes. Keep prompt/code/tests together unless the person requests another review route. If impact or rollback is unclear, propose the feature or bug recipe before expanding scope.

## Editable runner definition

The bundled `workflow.json` selects these steps and their semantic protocols. Copy the complete directory to your project at `.pdd/workflows/NAME/` to edit it or add a workflow. A project directory overrides the whole bundled recipe; it must include a valid JSON definition and every declared Markdown file. Run `pdd workflow list` to discover validated definitions. The runner saves the resolved definition, Markdown and full guide-first context before assigning the worktree. Source edits never silently alter an existing run; changed inputs refuse advancement. Make edits before a new run. Test commands come from the independently accepted proposal handoff, not executable JSON configuration.
