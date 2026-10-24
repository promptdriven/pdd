# Feature recipe

Use this for a new behavior with a prompt contract and implementation.

Use these instructions manually in your existing coding-agent conversation, or select this bundled workflow with `pdd workflow run NAME ISSUE` (replace NAME with this workflow's directory name). The local runner starts a fresh background native agent conversation for each agent step, supplies only the current stage request plus prior artifact pointers, pauses for recorded human choices, and uses normal Git/GitHub tools for actual PR stages. It does not execute prompts through a private service or merge PRs. In manual use, continue in your chosen conversation and publish only when asked.

When launched by the runner, obey the supplied current-stage request and handoff protocol. The overview does not authorize an agent to perform later steps. The runner owns push/PR creation; an agent must not duplicate those effects. The runner assigns a separate issue worktree and sends this saved current-stage request to a fresh owned background native conversation. Complete the real stage files and closed handoff, report the result, then stop working; no manual native exit is required. The foreground PDD controller waits for observed native activity and settlement, then independently validates the exact handoff, revisions, file hashes and required tests. Idle, a model turn or a handoff write alone never certifies success. Do not terminate the parent or launch a future stage. After the controller exits, advancement requires explicit resume of the saved run. Active attachment uses `pdd workflow attach RUN_ID`; completed stage history is archived rather than retained as a live pane.

## Before you begin

Before drafting any Story, read the **entire** [Prompting guide](../../../docs/prompting-guide.md) into this agent conversation, including in an existing chat. Summarize the relevant method: describe what and why, preserve observable behavior and consequential edge cases, give each rule one owner, and keep expected results independent of implementation. Then apply it. A link, filename, prior chat summary or format check does not load the guide. If the file is unavailable, ask for its contents before drafting.

Read repository instructions and relevant public interfaces. Follow the linked steps in order; adapt optional steps to the project and the person's request.

1. [Understand the request](understand.md)
2. [Choose a visual direction, if there is a UI](visual.md)
3. [Draft the prompt, Story and independent cases](prompt-story.md)
4. [Review the contract and cases](check.md)
5. [Try an ordinary project preview, when useful](try.md)
6. [Review the scope with the person](approve.md)
7. [Prepare a separate prompt PR only if requested](prompt-pr.md)
8. [Follow the agreed prompt review route](prompt-merge.md)
9. [Implement the agreed behavior](build.md)
10. [Run the real project tests](verify.md)
11. [Prepare a code PR if requested](code-pr.md)
12. [Leave merge to the person's normal process](code-merge.md)

A separate prompt PR is optional; the runner asks whether to execute or skip that stage. Prompts, Story, cases and code may share one reviewed change. When the existing prompt already covers the request, explain that and preserve it. Do not invent an edit or demand an extra approval when the person has already authorized this scope.

## Editable runner definition

The bundled `workflow.json` selects these steps and their semantic protocols. Copy the complete directory to your project at `.pdd/workflows/NAME/` to edit it or add a workflow. A project directory overrides the whole bundled recipe; it must include a valid JSON definition and every declared Markdown file. Run `pdd workflow list` to discover validated definitions. The runner saves the resolved definition, Markdown and full guide-first context before assigning the worktree. Source edits never silently alter an existing run; changed inputs refuse advancement. Make edits before a new run. Test commands come from the independently accepted proposal handoff, not executable JSON configuration.
