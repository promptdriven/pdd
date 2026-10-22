# Story: ticket status labels

Synthetic teaching example; this Story does not describe a real product or user.

## Acceptance criteria

1. `open`, `blocked`, and `done` return their corresponding title-cased labels.
2. Unknown strings and `null` return `Unknown` without throwing.
3. Values outside the declared input domain (strings and `null`) throw `TypeError`.
4. Matching is exact and case-sensitive; the function does not trim or normalize strings.

The independent expected values are in [`status-labels.json`](../vectors/status-labels.json). That file's shape is example-specific and is consumed by the local Node test only.
