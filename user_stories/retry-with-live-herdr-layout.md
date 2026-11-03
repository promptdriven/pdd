# Retry with the live Herdr layout

I can cancel a stuck workflow and start a fresh run from another checkout of the same clone, without editing PDD's saved layout state.

## Acceptance criteria

1. Starting a new run from a linked checkout starts its story chat even when an old layout registry points at another linked checkout of the same clone, contains an old run intent, and Herdr lists that old workspace without worktree metadata.
2. Starting or reopening uses the unique live run workspace for the assigned checkout and clone, and the area tab with the matching name and checkout; retrying an allocation adopts Herdr's verified "already_open" result without creating duplicates.
3. An existing non-linked workspace of this clone can serve as the parent, including one the person opened; other clones, ambiguous run matches and changed checkout identities cannot supply the run's workspace.
4. PDD neither reads nor changes its old layout registry; "pdd workflow status --all" discovers clones only through the run index.
5. Existing unrelated workspaces, labels, native sessions and Git checkouts stay intact. Cleanup preserves adopted parents and refuses to close a run with changed roots, extra tabs or extra panes.

## Rules to check

Live checkout path plus clone identity determine the run workspace. A stale registry, old linked source checkout or old refusal phase must never block a verified fresh allocation. Hold the find/create lock and checkpoint actual identities before chat dispatch. Missing or ambiguous live identity must never authorize adoption, duplicate allocation or destructive cleanup.

## Native regression

[test/workflow-herdr-live-layout.test.mjs](../test/workflow-herdr-live-layout.test.mjs) contains a synthetic local Git/Herdr regression for criterion 1 and the old-registry preservation part of criterion 4. It asserts actual chat dispatch and verifies the legacy workspace is retained. PR 1 marks the assertion as TODO because implementation follows in PR 2; `PDD_ENFORCE_LIVE_LAYOUT=1 node --test test/workflow-herdr-live-layout.test.mjs` enforces it and must fail against the unfixed implementation. Remove the TODO for PR 2.

The [native case inventory](../test/fixtures/workflow-herdr-live-layout.json) copies every criterion and records requirement-derived fixtures and exact expected effects for live reuse, label-plus-cwd matching, already_open, parent/clone identity, ambiguity, malformed registry, index-only status and safe cleanup. Only the first case has an executable regression in this prompt PR; the remaining native verifications are pending for PR 2, not claimed passing. This inventory is not an Interpreter scenario.

The owning module's filesystem identities, callback/checkpoint ports and lock are unbound to the Interpreter. No synthetic check-only API or JSON scenario is introduced. Paid prompt checks and simulations are excluded by the person's instruction; native tests do not prove a live Herdr or native-agent run.
