As a person using Gemini workflow chats, I want to reopen an ended area with its saved history even when Herdr missed its session ID, so that ending a pane or restarting the VM does not lose my conversation.

## Acceptance criteria

1. Reopening an ended Gemini area resumes the unique saved main session for its worktree, launch window and original account, even when Herdr never recorded its ID or the workspace closed.
2. Sessions from another worktree or outside that area's launch window, and subagent sessions, are never selected; multiple matching sessions or unreadable evidence never authorize a guessed resume.
3. When the current area’s session cannot be recovered, pdd gives one line naming the area and offering a fresh chat with `pdd workflow open N --new`; an explicit fresh choice works in the same area. A historical area keeps the existing restriction on fresh chats, and its diagnostic never offers to replace another area.
4. Gemini recovery reads legacy JSON and current JSONL session files, without modifying them or treating their messages as approval.

## Rules to check

Only exactly one distinct main session in the inclusive launch window and saved worktree/account may supply a recovered UUID. The forbidden result is selecting a foreign, ambiguous or out-of-window session.

```pdd-boundary
prompts/cli/workflow-chat.prompt.md
prompts/cli/approval-evidence.prompt.md
prompts/cli/workflow-runner.prompt.md
```
