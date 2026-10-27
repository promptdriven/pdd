# Small-change area-chat prompts

Own `src/workflow-area-chat-context.mjs`: assemble the instructions for the two
opt-in small-change main chats and their single-stage subagents. The runner owns
state, stage acceptance, approval evidence, tests, publication and session launch.
This module returns text only. Preserve existing non-chat recipe behavior and the
runner's exact supplied stage identities and handoff protocol.

`buildAreaChatInstructions({area, stageInstructions, reportCommand,
approvalCommand, resumeCommand, changesText, prompts})` is the runner integration entrypoint.
`area` is `{id,label,gate}` matching plan/Chat 1: plan/approve-plan or
build/Chat 2: build/merge. It returns instructions to append AFTER the runner's
full saved guide-first context. The runner supplies nonempty current-stage
instructions, exact report command (including run/stage/attempt arguments) and
issue-form approval command as trusted command strings. Build additionally
requires the exact resumeCommand for observing the person's GitHub merge. Preserve these strings
verbatim; this entrypoint does not tokenize or reconstruct them. Reject line
breaks/NUL in command strings. Optional `changesText` (absent or null means none) is trusted runner guidance
for the supported change route. Optional `prompts` is the saved template object;
if absent load bundled texts for an initial run. The runner must persist the
rendered result or templates for recovery. Include the current stage packet and
stage task references for this area. The main chat uses the exact current report
command, reads `nextStageInstructions` and the next report command from PDD,
then delegates in the SAME main session until a waiting gate. Never reuse a prior
attempt's report command. PDD-owned PR/merge stages run only as directed by PDD.

`loadAreaChatPrompts()` reads the bundled UTF-8 area-chat texts into a plain object.
The caller saves that object in the run snapshot and passes it to both builders;
rendering never reloads mutable files. Missing or empty texts fail explicitly.

`buildAreaChatPrompt({area, agent, issueNumber, runId, context, prompts,
pddCommand})` returns the complete saved guide-first context followed by the
common rules, area instructions and native delegation instructions. `area` is
`plan` or `build`; `agent` is `codex` or `claude`. The runner supplies a nonempty
run ID, positive safe-integer issue number and nonempty saved context containing
the full guide and selected workflow. It must supply the current verified stage
packet separately when available; this builder never invents attempts or marks a
stage accepted. The two labels are `Chat 1: plan` and `Chat 2: build`.

`buildAreaStageTask({stageId, instructions, prompts, pddCommand})` returns the
stage-specific task followed by the nonempty exact runner instructions, preserved
verbatim. Supported stage IDs are `scope`, `change`, `verify`, `open-pr` and
`wait-merge`. The latter two delegate review only: PDD still performs publication
and merge observation. The main chat reports each agent stage using the exact
`pdd step done <stage>` command and waits for PDD acceptance. PR and merge are
runner-owned effects, not mandatory report commands; after verify the runner may
perform publication and return its merge wait directly. A failed/uncertain
report stops progression, including after recovery; a subagent's prose is never
acceptance. The supplied instructions remain authoritative for closed handoff
fields, paths and identities.

The templates own the human gate wording, stage tasks and crash rules. Chat
approval requires the person's new user message after the gate question and
PDD's native-session evidence check. A refusal cannot become agent approval.
Build starts in a new main session after recorded plan approval. At merge wait
there is no approve decision: the person merges using the normal GitHub process,
then runs the supplied resumeCommand so PDD observes that exact merge. Never
suggest workflow approve or relay a chat approval at the merge gate.

## Dependencies

- [Prompting guide](../../docs/prompting-guide.md): authoring and verification.
- [Bundled small-change definition](../../.pdd/workflows/small-change/workflow.json)
  and its declared Markdown files: stage semantics, authoring and testing; their
  saved full context is required at runtime via `context`/`instructions`.
- [Common](../../.pdd/workflows/small-change/area-chats/common.md),
  [plan](../../.pdd/workflows/small-change/area-chats/plan.md),
  [build](../../.pdd/workflows/small-change/area-chats/build.md),
  [scope](../../.pdd/workflows/small-change/area-chats/scope.md),
  [change](../../.pdd/workflows/small-change/area-chats/change.md),
  [verify](../../.pdd/workflows/small-change/area-chats/verify.md),
  [open-pr](../../.pdd/workflows/small-change/area-chats/open-pr.md), and
  [wait-merge](../../.pdd/workflows/small-change/area-chats/wait-merge.md):
  required complete runtime texts, loaded by `loadAreaChatPrompts` and snapshotted
  by the caller. Node's filesystem and URL support resolve these from the package,
  independent of project cwd.

<details>
<summary>Command rendering, input failures and template substitution</summary>

`pddCommand` defaults to `['pdd']`; otherwise it is a nonempty array of nonempty
strings without NUL or line breaks, representing the actual executable and fixed
arguments, not shell source. Quote each argument for a POSIX shell, preserving
spaces, quotes and metacharacters literally. Append report/approval arguments as
separate words. Generated commands use the assigned worktree cwd. Do not execute
them from this module. Never silently fall back from an invalid supplied prefix.

`prompts` must contain all eight nonempty strings named by their filenames without
`.md`. Replace only `{{approveCommand}}`, `{{resumeCommand}}`, `{{scopeCommand}}`,
`{{changeCommand}}`, `{{verifyCommand}}`, `{{openPrCommand}}` and
`{{waitMergeCommand}}` in template text. Do not interpolate supplied context,
identities or runner instructions as templates. Invalid inputs throw an Error
naming the affected field; unknown area/stage/agent must never select a default.
No state writes, model calls, shell effects or global configuration changes.

</details>
