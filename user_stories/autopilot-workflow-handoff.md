# Keep my selected account in Autopilot issue runs

I can let Autopilot start a visible PDD issue run with the same installed PDD and account that I selected for Autopilot.

## Acceptance criteria

1. Each launcher packet identifies the invoked package's absolute PDD command and selected agent family.
2. The packet carries the selected home and config-folder binding, including a configured launcher's override, even when a later tool shell uses another profile or the native coordinator pane is recreated. The recreated coordinator uses those saved bindings too. If the named launcher changes agent family, it reports that I must start Autopilot again and leaves the work pending.
3. The packet contains no credentials or unrelated environment values. Other native child environment values, issue text and pending delivery keep their existing behavior.
4. Autopilot runs the recipe first, claims the issue, then starts or reuses its normal PDD run before issue edits or delegation. The run owns its worktree, chats, gates and PRs.

## Scope

These criteria cover native coordinator bindings, packet metadata and the explicit
PDD command route. The intended same-account issue run also needs default-home
bindings in PDD child chats. That shared workflow behavior remains a known gap;
a correct packet alone does not prove it.
