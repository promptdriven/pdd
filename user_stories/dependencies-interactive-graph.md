# Explore the dependency graph

I can find an issue in the interactive graph and read the reasons for its state.

## Acceptance criteria

1. The graph shows search, status filters, the graph and selected issue reasons, with the last successful sync and refreshing or offline state.
2. Search and filters retain matching nodes and their prerequisite context without changing readiness. Selecting issue 42 shows its blocker reason and evidence.
3. A running filter uses actual execution state. Unknown work remains labeled unknown, and no matching issue gives an empty result rather than invented readiness.
4. An offline update keeps the selected issue and its reasons. The layout stacks details below the graph when the panes cannot fit side by side.

5. A saved deployment question shows its exact text, owning issue and source after restart. A trusted replacement updates those facts. With no cache the viewer shows "No saved graph" and no ready work.

## Rules to check

The UI cannot add a dependency, decide trust or infer readiness. Search/filter retain prerequisite context. SVG references own relationships and layout; native browser verification must check keyboard access, pan/zoom, inert private text, cached first paint, background updates, narrow stacking and the actual Screen against both drawings. Runtime facts do not prove those appearance/host effects.
