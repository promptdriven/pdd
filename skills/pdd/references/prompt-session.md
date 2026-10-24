# Prompt work in your existing conversation

Read the entire [canonical Prompting guide](../../../docs/prompting-guide.md) in the actual conversation before any Story or prompt authoring. Explain the rules relevant to the next change, then use them. Loading only this reference or a Story schema is insufficient.

## Start from the actual folder

Use the person's installed native agent and selected project checkout, launched through the local session command or opened normally. The launcher must load the complete guide and bundled workflow context before Story drafting, preserving native login and global settings while starting agents in full-access mode without approval prompts. Inspect project guidance, available files and the requested scope. Give a brief useful summary; if they already provided a task, start it without asking them to repeat it. Small changes need not adopt prompt space for the entire project.

When invoking PDD inside a native conversation, keep the supplied actual package command prefix, including an absolute Node executable path when given. Use that entrypoint for help, list, run, resume and attach, preserving the assigned project cwd. Bare `pdd` can resolve to another installation in the native login shell even when the outer terminal resolves this alpha. If the package path is not known, resolve the intended package before invoking PDD; do not substitute a private/global command or edit shell profiles to work around the mismatch.

For a new project, agree on its useful first behavior and use a real project directory. Git/GitHub project creation uses available tools only when requested; it is not a PDD service action. Missing GitHub access does not prevent local drafting. Do not copy credentials or switch accounts as a workaround.

## Draft from intent and evidence

Use the guide to choose module boundaries and document behavior, inputs, outcomes, errors and preservation. In a new project, `prompts/<module>.prompt.md` can be a useful convention; existing layouts take precedence. Required contracts belong in the guide's Dependencies declaration with resolvable paths; navigation links alone do not load them.

Write a Story describing the person's useful outcome and observable criteria. Derive independent cases for normal behavior, boundaries and errors from the intended contract. Keep design questions visible and ask for the decision that changes the result. Do not infer approval from an existing implementation or from a model-generated test passing.

For adoption, inspect code, callers, tests and source documentation; keep implementation unchanged until requested. Distinguish observed behavior from accepted policy and mark unavailable context. Do not invent an execution-service interface or require standalone lint to finish a draft.

## Continue in the same conversation

Show the prompt, Story and cases for review. Follow [review guidance](review.md). When the person requests implementation, use their agent's actual coding tools and the project's native tests. Keep expected results independent of the implementation under test. If a test fails, report and investigate the failure rather than changing expectations to match it.

Choose [workflow guidance](../../../docs/workflows.md) for a requested local issue run with fresh agent-stage sessions, saved run state, human waits and real PR stages. Preserve the returned run identity; native exit zero alone is not stage evidence. A manually followed recipe or single-conversation shortcut does not create that runner state. Reopen or resume the native agent through that agent's normal supported controls, preserving project files and the actual conversation. The local session launcher opens the native agent; it does not supply a hosted-service session.

## Complete the current runner stage

Follow only the supplied current-stage instructions in its assigned issue worktree. Load and apply the full guide and saved selected-workflow context before authoring. Complete the real required files and exact closed JSON handoff, then report the result. Do not start a later stage or alter another issue's worktree.

The background-stage controller supplies one owned prompt to a fresh agent and observes its activity/readiness. The runner independently validates the exact handoff, hashes, current revision and actual required tests before accepting and starting a fresh next stage. Readiness alone is not success; no fabricated native turn ID or process exit is needed. Ordinary `pdd session` is still a foreground conversation.

If a person attaches, preserve the actual active stage identity. Interaction or changed artifacts invalidates an earlier candidate; the runner must freshly validate after detachment before acceptance/cleanup. Do not terminate the parent controller, close uncertain work or submit duplicate prompts to force progress. Controller exit ends automatic PDD progression; explicit saved-run resume reconciles original work. Completed archived stage panes are not promised live.

Report what was written, reviewed, implemented and actually checked. If a tool is unavailable, name the gap. Never label an unavailable check as passed or claim a local project test executed prompts through PDD.
