# Foreground workflow progress

Own src/workflow-progress.mjs. Export createWorkflowProgress({stdout,now}), returning observe(event) and interrupt(). This is a renderer, with no repository reads, run allocation, stage effects or decisions. A person starting an issue run must immediately see that PDD is working, learn the saved run and agent location, review the proposal at a gate, and find that same run after an interruption. Preserve 0.1.0 identities and controller semantics.

Print the full run ID, workflow, issue, current stage ordinal/count, worktree, branch, journal file and exact pdd workflow attach UUID when the actual run becomes known. Print actual Herdr session/workspace as checkpointed, once per new identity; never substitute the default session or claim a workspace before it exists. Reuse the plain timestamped stage-start/stage-end and summary/read/approve/PR formatting of the existing watch design, without importing newer commands or state layout.

Each agent/PR intent prints a timestamped stage start. Completion, skip, human approval and test execution changes print timestamped lines tied to the actual stage. Repeated backend polling adds no repeated lines. Result states print a timestamped stage state. At a waiting gate show accepted artifact JSON and project file paths plus a short agent summary, preserving any recommendation contained in it, and the exact full-ID resume --decision approve command. Optional gates also show --decision skip. For an unresolved pending stage print inspect and attach guidance; do not call it approved. Merge waits show saved PR links, say the person must merge, and use no-decision resume. Always print known PR URLs at final results. Show the runner's actual final message separately, once, through the CLI.

Collapse terminal control characters and newlines in all interpolated values. Keep summaries to a short readable line. Do not shorten IDs in executable commands. Observations must not mutate caller data. Track state only within this renderer instance. interrupt() prints that the foreground controller stopped and the agent may keep working in Herdr, then the known attach/inspection commands and an explicit approve command for continuing after inspection. Before an identity is known, explain that preparation was interrupted and point to the repository's existing .git/pdd/workflow-inputs directory; never fabricate a run ID or promise continuation.

## Dependencies

- [Runner](workflow-runner.prompt.md) owns event facts, run identities and all execution/approval semantics.
- [CLI](pdd-cli.prompt.md) owns immediate startup output, signal lifetime, exit status and the one final result message.
- [Prompting guide](../../docs/prompting-guide.md) governs this contract's authoring.
