# PDD issue handoff

Required step for pdd-autopilot. After the recipe and claim, check `pdd workflow status N`.
Reuse an active run with `pdd workflow open N`; otherwise start
`pdd workflow run bug|feature|small-change N --agent AGENT` with the matching workflow
and the packet's agent, or the current agent without a packet. Use the normal PDD
session before issue edits or delegation. The run owns its worktree, area chats,
gates and PRs; do not create issue worktrees or PRs outside it.

With a launcher `workflow` packet, use its absolute `pddBin` for PDD commands.
Bind HOME to `home`. If `configHome` is present, bind its `variable` to `path`,
or unset that variable when the path is null. Shell-quote paths. Apply these
bindings to workflow commands and ensure supported workflow routes inherit the
selected explicit profile for new chats. Without a packet, use installed pdd and the current
profile. These command bindings do not alone prove that a default-home profile
reaches issue chats in an existing normal PDD server.
