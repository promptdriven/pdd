# Generate CLI reference command tables

As a maintainer updating pdd CLI commands, I want the CLI reference command tables generated from the command catalog inside explicit markers, so that parallel feature changes stop colliding in hand-edited tables and stale or conflicted generated blocks recover cleanly.

## Acceptance criteria

1. Syncing a CLI reference with commands across "Core PDD workflow", "Cloud accounts", and "Autopilot" writes one table row per command in group order inside the generated markers, escapes pipe characters such as `pdd autopilot start [--mode auto|observe]` and flattens multi-line descriptions to one line, keeps every byte outside the markers unchanged, and reports that the document changed.
2. Checking a CLI reference whose generated tables already match the catalog returns status "current" with zero missing or extra forms, and syncing it again reports no change.
3. Checking a CLI reference whose generated tables are missing `pdd accounts list [--json]` and still list removed command `pdd old-cmd` returns status "stale" with `pdd accounts list [--json]` in missing forms and `pdd old-cmd` in extra forms.
4. When Git merge conflict lines appear only inside the generated markers, checking returns status "conflict", default sync refuses with error "generated-conflict", and conflict-resolving sync replaces the conflicted block with clean regenerated tables, leaves zero conflict markers, and reports conflicts resolved.
5. When Git merge conflict lines appear in hand-written prose outside the generated markers, both sync and check refuse with error "prose-conflict" so hand-written prose conflicts are never overwritten.
6. When the start or end generated marker is missing, duplicated, or out of order, syncing refuses with "missing-markers", "duplicate-markers", or "misordered-markers".

## Rules to check

- Hand-written prose, headings, and anchor links outside the generated markers must stay byte-for-byte unchanged. Forbidden: rewriting prose outside markers or resolving conflicts outside markers.
- Generated tables must never emit unescaped pipes, multi-line table cells, or remaining Git conflict markers. Forbidden: silently dropping prose conflicts or mutating a document with invalid markers.
